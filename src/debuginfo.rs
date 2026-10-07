//! Debug-info type recovery from textual LLVM IR.
//!
//! Under LLVM 15+ opaque pointers a `getelementptr` no longer carries the pointee's
//! struct type, so the PAG's field-sensitivity degrades: a GEP into a struct looks the
//! same as a GEP into any other allocation, and two distinct resources reached through
//! `ptr` can collapse into one points-to set. The DWARF-style debug metadata that rustc
//! emits with `-C debuginfo=2`, however, still records the real struct layouts and the
//! types of every local and parameter. This module recovers that.
//!
//! The `llvm-ir` crate we build the PAG on (0.11) does not parse the `!DI*` metadata
//! graph at all (`metadata_nodes` is a `--TODO not yet implemented--`; only `DebugLoc`
//! file/line is exposed). So this module scans the textual `.ll` itself for the debug
//! metadata nodes and reconstructs:
//!
//!   * struct layouts: `DICompositeType` -> ordered `DIDerivedType(DW_TAG_member)`
//!     entries, each with a field name, bit offset, and bit size;
//!   * the type of every alloca/parameter: `#dbg_declare(ptr %v, !var, ...)` ->
//!     `DILocalVariable(type: !ty)`, with pointer/typedef/const wrappers stripped down
//!     to the underlying composite.
//!
//! With this, a field-sensitive consumer can map an opaque-pointer GEP (`%f = getelementptr
//! i8, ptr %base, i64 OFFSET`) back to the named field: recover `%base`'s struct via
//! [`DebugTypes::value_composite`] and resolve `OFFSET` with [`DebugTypes::resolve_member`].
//!
//! The metadata subset is regular, so this is a focused line scanner rather than a full
//! LLVM-IR metadata parser; it reads only the node kinds it needs and ignores the rest.

use llvm_ir::instruction::Instruction;
use llvm_ir::{Constant, Module, Operand, Type};
use std::collections::{HashMap, HashSet};
use std::path::Path;

/// A metadata node id, the `N` in a textual `!N` reference.
pub type MetaId = u64;

/// An SSA value's recovered type during propagation: either a whole struct, or a field of
/// a struct at a given bit offset (reached through a byte-offset GEP).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValTy {
    Struct(MetaId),
    Field { parent: MetaId, offset_bits: u64 },
    /// A pointer to a coroutine/async env (its captures are typed by byte offset).
    EnvBase,
}

/// The result of [`DebugTypes::propagate_types`]: a map from `(function, %value)` to a
/// stable type token string (a struct name, or `Struct.field` for a scalar field), for
/// every SSA value whose debug type could be propagated.
#[derive(Debug, Default)]
pub struct ValueTypes {
    tokens: HashMap<(String, String), String>,
    /// `(function, %value) -> coroutine env capture byte offset`, for values that are or
    /// derive from an async `env` capture. Two values in the same function with the same
    /// offset are the same captured instance, so sites using them share a resource.
    captures: HashMap<(String, String), u64>,
}

impl ValueTypes {
    /// The recovered type token of an SSA value, if any. `value` is the name as it appears
    /// in the IR (e.g. `%r` or `%0`).
    pub fn token(&self, func: &str, value: &str) -> Option<&str> {
        self.tokens
            .get(&(func.to_string(), value.to_string()))
            .map(|s| s.as_str())
    }

    /// The coroutine env capture offset an SSA value resolves to, if it is a captured
    /// variable. Same function + same offset means the same captured instance.
    pub fn capture_offset(&self, func: &str, value: &str) -> Option<u64> {
        self.captures
            .get(&(func.to_string(), value.to_string()))
            .copied()
    }

    /// Number of typed values recovered (for diagnostics).
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Number of typed values in a given function (for diagnostics).
    pub fn count_for(&self, func: &str) -> usize {
        self.tokens.keys().filter(|(f, _)| f == func).count()
    }

    /// A sample of typed entries `(func, value, token)` for diagnostics.
    pub fn sample(&self, n: usize) -> Vec<(String, String, String)> {
        self.tokens
            .iter()
            .take(n)
            .map(|((f, v), t)| (f.clone(), v.clone(), t.clone()))
            .collect()
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }
}

/// One field of a struct, recovered from a `DIDerivedType(tag: DW_TAG_member, ...)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Member {
    pub name: String,
    /// Bit offset of the field within the enclosing struct (0 when `offset:` is absent).
    pub offset_bits: u64,
    /// Bit size of the field (0 when `size:` is absent).
    pub size_bits: u64,
    /// The field's own type node (`baseType:`), for recursing into nested structs.
    pub base_type: MetaId,
}

/// A recovered struct layout, from a `DICompositeType(tag: DW_TAG_structure_type, ...)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLayout {
    pub name: String,
    pub size_bits: u64,
    pub members: Vec<Member>,
}

/// A parsed `DICompositeType` header (members are expanded lazily via its elements tuple).
#[derive(Debug, Clone)]
struct Composite {
    name: String,
    size_bits: u64,
    elements: Option<MetaId>,
}

/// A parsed `DILocalVariable`.
#[derive(Debug, Clone)]
struct LocalVar {
    #[allow(dead_code)]
    name: String,
    /// `Some(n)` for the n-th parameter, `None` for an ordinary local.
    #[allow(dead_code)]
    arg: Option<u32>,
    /// The variable's declared type node (`type:`).
    ty: Option<MetaId>,
}

/// The recovered debug-info type graph for one module.
#[derive(Debug, Default)]
pub struct DebugTypes {
    /// `DICompositeType` nodes (structs / tuples / enums laid out as structs).
    composites: HashMap<MetaId, Composite>,
    /// `DIDerivedType(DW_TAG_member)` nodes, keyed by their own id.
    members: HashMap<MetaId, Member>,
    /// `DIDerivedType` wrapper nodes (pointer / reference / typedef / const / etc.):
    /// id -> the node it wraps (`baseType:`). Used to strip down to a composite.
    derived_base: HashMap<MetaId, MetaId>,
    /// `!N = !{ !a, !b, ... }` tuple nodes.
    tuples: HashMap<MetaId, Vec<MetaId>>,
    /// `DILocalVariable` nodes.
    locals: HashMap<MetaId, LocalVar>,
    /// `(function mangled name, ssa value name without the leading `%` and `.dbg.spill`
    /// suffix) -> DILocalVariable id`, from `#dbg_declare` / `llvm.dbg.declare`.
    value_var: HashMap<(String, String), MetaId>,
    /// Raw `#dbg_declare` targets `(function, value name without `%` but WITH any
    /// `.dbg.spill` suffix, DILocalVariable id)`, used to seed type propagation on both the
    /// spill alloca and the source-named value. Only plain declares (no `DW_OP_deref`).
    dbg_decls: Vec<(String, String, MetaId)>,
    /// Coroutine/async captures: `function -> [(byte offset in the env, DILocalVariable id)]`,
    /// from `#dbg_declare(ptr %env, !var, DIExpression(DW_OP_deref[, DW_OP_plus_uconst, N]))`.
    /// The captured variable lives at `N` inside the dereferenced env, which is how async
    /// state machines store their locals; code reads them via `getelementptr i8, env, N`.
    captures: HashMap<String, Vec<(u64, MetaId)>>,
    /// Env-slot values: `function -> {value names}` that hold the coroutine env pointer (the
    /// first operand of a `DW_OP_deref` dbg_declare). A load of such a slot yields the env.
    env_slots: HashMap<String, std::collections::HashSet<String>>,
}

impl DebugTypes {
    /// Parse a textual `.ll` file. Returns an empty (but valid) instance on read error or
    /// when the module carries no debug info, so callers can use it unconditionally.
    pub fn parse_file(path: &Path) -> DebugTypes {
        match std::fs::read_to_string(path) {
            Ok(text) => DebugTypes::parse_str(&text),
            Err(_) => DebugTypes::default(),
        }
    }

    /// Parse several `.ll` files into one instance. Each file has its own `!N` metadata id
    /// space, so ids are offset into disjoint ranges before merging to avoid collisions.
    /// Function names are globally unique (mangled), so the `(function, value)` links never
    /// collide. Unreadable files are skipped.
    pub fn parse_files<P: AsRef<Path>>(paths: impl IntoIterator<Item = P>) -> DebugTypes {
        let mut combined = DebugTypes::default();
        let mut offset: MetaId = 0;
        for p in paths {
            let Ok(text) = std::fs::read_to_string(p.as_ref()) else { continue };
            let one = DebugTypes::parse_str(&text);
            let next = one.max_meta_id().map(|m| offset + m + 1);
            combined.absorb(one, offset);
            if let Some(n) = next {
                offset = n;
            }
        }
        combined
    }

    /// The largest metadata id seen, if any (used to compute a disjoint offset for merging).
    fn max_meta_id(&self) -> Option<MetaId> {
        self.composites
            .keys()
            .chain(self.members.keys())
            .chain(self.derived_base.keys())
            .chain(self.tuples.keys())
            .chain(self.locals.keys())
            .copied()
            .max()
    }

    /// Merge `other` into `self`, shifting all of `other`'s metadata ids by `offset`.
    fn absorb(&mut self, other: DebugTypes, offset: MetaId) {
        for (id, mut c) in other.composites {
            c.elements = c.elements.map(|e| e + offset);
            self.composites.insert(id + offset, c);
        }
        for (id, mut m) in other.members {
            m.base_type += offset;
            self.members.insert(id + offset, m);
        }
        for (id, base) in other.derived_base {
            self.derived_base.insert(id + offset, base + offset);
        }
        for (id, elems) in other.tuples {
            self.tuples
                .insert(id + offset, elems.into_iter().map(|e| e + offset).collect());
        }
        for (id, mut lv) in other.locals {
            lv.ty = lv.ty.map(|t| t + offset);
            self.locals.insert(id + offset, lv);
        }
        for (k, v) in other.value_var {
            self.value_var.insert(k, v + offset);
        }
        for (f, v, var) in other.dbg_decls {
            self.dbg_decls.push((f, v, var + offset));
        }
        for (f, caps) in other.captures {
            let e = self.captures.entry(f).or_default();
            for (off, var) in caps {
                e.push((off, var + offset));
            }
        }
        for (f, slots) in other.env_slots {
            self.env_slots.entry(f).or_default().extend(slots);
        }
    }

    /// Parse textual LLVM IR from a string.
    pub fn parse_str(text: &str) -> DebugTypes {
        let mut dt = DebugTypes::default();
        let mut current_fn: Option<String> = None;

        for line in text.lines() {
            let t = line.trim_start();

            // Track the enclosing function body so dbg_declare maps to the right scope.
            if t.starts_with("define ") {
                // Normalize so the keys match the PAG's `SSAValue.function`
                // (`util::normalize_function_name`): the textual define keeps the quotes
                // around special symbols (`@"_ZN...$u7b$...E"`), which the PAG strips.
                current_fn =
                    parse_define_name(t).map(|n| crate::util::normalize_function_name(&n).to_string());
                continue;
            }
            if line.starts_with('}') {
                current_fn = None;
                // keep scanning: metadata nodes live at top level after the bodies
            }

            // dbg_declare inside a function body links an SSA value to a DILocalVariable.
            if let Some((val, var, env_off)) = parse_dbg_declare(t) {
                if let Some(func) = &current_fn {
                    match env_off {
                        // A DW_OP_deref dbg_declare: `var` is a coroutine/async capture living
                        // at byte offset `off` inside the env pointer held by `val`.
                        Some(off) => {
                            dt.captures.entry(func.clone()).or_default().push((off, var));
                            dt.env_slots
                                .entry(func.clone())
                                .or_default()
                                .insert(format!("%{}", strip_value_suffix(&val)));
                        }
                        // A plain dbg_declare: `var` is stored directly at `val`.
                        None => {
                            let key = strip_value_suffix(&val).to_string();
                            dt.value_var.insert((func.clone(), key), var);
                            dt.dbg_decls.push((func.clone(), val, var));
                        }
                    }
                }
                continue;
            }

            // Top-level metadata node: `!N = ...`
            if let Some((id, body)) = parse_meta_line(t) {
                dt.ingest_meta(id, body);
            }
        }
        dt
    }

    fn ingest_meta(&mut self, id: MetaId, body: &str) {
        if body.starts_with("!{") {
            // tuple: !{ !a, !b, ... }
            self.tuples.insert(id, parse_ref_list(body));
        } else if body.starts_with("!DICompositeType(") {
            // only structure/class/union layouts carry members we care about
            let name = str_field(body, "name:").unwrap_or_default();
            let size_bits = num_field(body, "size:").unwrap_or(0);
            let elements = ref_field(body, "elements:");
            self.composites.insert(id, Composite { name, size_bits, elements });
        } else if body.starts_with("!DIDerivedType(") {
            if let Some(tag) = ident_field(body, "tag:") {
                if tag == "DW_TAG_member" {
                    let name = str_field(body, "name:").unwrap_or_default();
                    let offset_bits = num_field(body, "offset:").unwrap_or(0);
                    let size_bits = num_field(body, "size:").unwrap_or(0);
                    let base_type = ref_field(body, "baseType:").unwrap_or(0);
                    self.members.insert(id, Member { name, offset_bits, size_bits, base_type });
                } else {
                    // pointer / reference / typedef / const / volatile / atomic wrapper
                    if let Some(base) = ref_field(body, "baseType:") {
                        self.derived_base.insert(id, base);
                    }
                }
            }
        } else if body.starts_with("!DILocalVariable(") {
            let name = str_field(body, "name:").unwrap_or_default();
            let arg = num_field(body, "arg:").map(|n| n as u32);
            let ty = ref_field(body, "type:");
            self.locals.insert(id, LocalVar { name, arg, ty });
        }
        // DIBasicType / DISubprogram / DIFile / DILocation etc. are not needed here.
    }

    /// Follow pointer/reference/typedef/const wrappers from a type node down to the
    /// underlying `DICompositeType`, returning its id. Returns `None` for a non-struct
    /// (e.g. a pure scalar) or an unresolved node. Cycle-safe.
    pub fn strip_to_composite(&self, mut id: MetaId) -> Option<MetaId> {
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(id) {
                return None; // defensive: metadata cycle
            }
            if self.composites.contains_key(&id) {
                return Some(id);
            }
            match self.derived_base.get(&id) {
                Some(&base) => id = base,
                None => return None,
            }
        }
    }

    /// Build the full field layout of the composite `id`, expanding its elements tuple.
    pub fn struct_layout(&self, id: MetaId) -> Option<StructLayout> {
        let comp = self.composites.get(&id)?;
        let mut members = Vec::new();
        if let Some(tuple) = comp.elements.and_then(|e| self.tuples.get(&e)) {
            for m in tuple {
                if let Some(mem) = self.members.get(m) {
                    members.push(mem.clone());
                }
            }
        }
        Some(StructLayout { name: comp.name.clone(), size_bits: comp.size_bits, members })
    }

    /// The composite (struct) that an SSA value's debug type resolves to, if any.
    /// `value` is the SSA name without the leading `%` (and `.dbg.spill` is tolerated).
    pub fn value_composite(&self, func: &str, value: &str) -> Option<MetaId> {
        let key = (func.to_string(), strip_value_suffix(value).to_string());
        let var = self.value_var.get(&key)?;
        let ty = self.locals.get(var)?.ty?;
        self.strip_to_composite(ty)
    }

    /// The struct type *name* an SSA value resolves to, if its debug type is a composite.
    /// This is the signature a consumer hashes into a resource/type tag. `value` is the SSA
    /// name without the leading `%` (a `.dbg.spill` suffix is tolerated).
    pub fn value_type_name(&self, func: &str, value: &str) -> Option<&str> {
        let id = self.value_composite(func, value)?;
        self.composites.get(&id).map(|c| c.name.as_str())
    }

    /// Resolve a byte offset within a composite to the field that contains it.
    /// Picks the member whose `[offset, offset+size)` byte range contains `offset_bytes`;
    /// falls back to an exact bit-offset match when sizes are absent.
    pub fn resolve_member(&self, composite_id: MetaId, offset_bytes: u64) -> Option<Member> {
        let layout = self.struct_layout(composite_id)?;
        let off_bits = offset_bytes.checked_mul(8)?;
        // containment match first
        if let Some(m) = layout.members.iter().find(|m| {
            m.size_bits > 0 && off_bits >= m.offset_bits && off_bits < m.offset_bits + m.size_bits
        }) {
            return Some(m.clone());
        }
        // exact start-offset match (sizes unknown)
        layout.members.iter().find(|m| m.offset_bits == off_bits).cloned()
    }

    /// Reduce a value type to the composite it ultimately refers to (following one field
    /// hop). `Struct(id) -> id`; `Field -> the composite the field's own type strips to`.
    fn reduce(&self, v: ValTy) -> Option<MetaId> {
        match v {
            ValTy::Struct(id) => Some(id),
            ValTy::Field { parent, offset_bits } => {
                let m = self.resolve_member(parent, offset_bits / 8)?;
                self.strip_to_composite(m.base_type)
            }
            ValTy::EnvBase => None,
        }
    }

    /// The type of a value loaded *through* a pointer value of type `v`: the pointee struct
    /// of the field (or offset-0 field) that `v` designates, when that is itself a struct.
    fn load_result(&self, v: ValTy) -> Option<ValTy> {
        let (parent, off) = match v {
            ValTy::Field { parent, offset_bits } => (parent, offset_bits / 8),
            ValTy::Struct(id) => (id, 0),
            ValTy::EnvBase => return None,
        };
        let m = self.resolve_member(parent, off)?;
        self.strip_to_composite(m.base_type).map(ValTy::Struct)
    }

    /// Render a value type to a stable token string for resource binding: the struct name
    /// for a whole struct or a struct-typed field, else `Struct.field` for a scalar field.
    fn render(&self, v: ValTy) -> Option<String> {
        match v {
            ValTy::Struct(id) => self.composites.get(&id).map(|c| c.name.clone()),
            ValTy::Field { parent, offset_bits } => {
                let pname = self.composites.get(&parent)?.name.clone();
                if let Some(m) = self.resolve_member(parent, offset_bits / 8) {
                    if let Some(cid) = self.strip_to_composite(m.base_type) {
                        if let Some(c) = self.composites.get(&cid) {
                            return Some(c.name.clone());
                        }
                    }
                    return Some(format!("{}.{}", pname, m.name));
                }
                Some(format!("{}@{}", pname, offset_bits))
            }
            ValTy::EnvBase => None,
        }
    }

    /// Propagate recovered debug types from named source variables through the SSA dataflow
    /// (GEP / load / store / bitcast) so that compiler-generated *temporaries* carry a type.
    /// This is what connects the type recovery to real access sites, whose resource pointer
    /// is usually a temporary (a GEP result or a value loaded from a spill), not a named
    /// `let`. SSA is single-assignment, so propagation is first-writer-wins and monotone; a
    /// few passes handle use-before-def ordering. Returns a `(function, %value) -> token`
    /// map. Only byte-offset (`i8`) GEPs are typed (the opaque-pointer shape rustc emits);
    /// typed-aggregate GEPs are left for the points-to analysis.
    pub fn propagate_types<'a>(&self, modules: impl IntoIterator<Item = &'a Module>) -> ValueTypes {
        let mut out = ValueTypes::default();
        if self.is_empty() {
            return out;
        }
        for m in modules {
            for f in &m.functions {
                // Normalize to match the parse-time keys and the PAG's `SSAValue.function`.
                let fname_owned = crate::util::normalize_function_name(&f.name).to_string();
                let fname = &fname_owned;
                // value type and "contents behind this pointer" (for store/load round-trips)
                let mut cur: HashMap<String, ValTy> = HashMap::new();
                let mut contents: HashMap<String, ValTy> = HashMap::new();
                // value -> coroutine env capture offset (instance identity of a captured var)
                let mut cur_cap: HashMap<String, u64> = HashMap::new();

                // Seed from every dbg_declare in this function: both the raw target (the
                // spill alloca, e.g. `%r.dbg.spill`) and the source-named value (`%r`, which
                // rustc often uses for the parameter directly at -O0).
                for (df, raw, var) in &self.dbg_decls {
                    if df != fname {
                        continue;
                    }
                    let Some(cid) = self
                        .locals
                        .get(var)
                        .and_then(|lv| lv.ty)
                        .and_then(|t| self.strip_to_composite(t))
                    else {
                        continue;
                    };
                    cur.entry(format!("%{}", raw)).or_insert(ValTy::Struct(cid));
                    cur.entry(format!("%{}", strip_value_suffix(raw)))
                        .or_insert(ValTy::Struct(cid));
                }

                // Coroutine/async env: the slot values that hold the env pointer, and the
                // byte-offset -> captured composite map (the captures live inside the env).
                let empty_slots = std::collections::HashSet::new();
                let env_slots = self.env_slots.get(fname).unwrap_or(&empty_slots);
                let cap_offsets: HashMap<u64, MetaId> = self
                    .captures
                    .get(fname)
                    .map(|caps| {
                        caps.iter()
                            .filter_map(|(off, var)| {
                                let cid = self
                                    .locals
                                    .get(var)
                                    .and_then(|lv| lv.ty)
                                    .and_then(|t| self.strip_to_composite(t))?;
                                Some((*off, cid))
                            })
                            .collect()
                    })
                    .unwrap_or_default();

                for _ in 0..3 {
                    let mut changed = false;
                    for bb in &f.basic_blocks {
                        for inst in &bb.instrs {
                            match inst {
                                Instruction::GetElementPtr(g) if is_byte_gep(&g.source_element_type) => {
                                    if let (Some(base), Some(off)) =
                                        (operand_name(&g.address), gep_const_offset(&g.indices))
                                    {
                                        let base_ty = cur.get(&base).copied();
                                        // Coroutine env capture: a GEP into the env at a known
                                        // capture offset yields that captured variable's type.
                                        if base_ty == Some(ValTy::EnvBase) {
                                            if let Some(&cid) = cap_offsets.get(&off) {
                                                changed |= insert_first(
                                                    &mut cur,
                                                    g.dest.to_string(),
                                                    ValTy::Struct(cid),
                                                );
                                                // record the capture instance identity (offset)
                                                if let std::collections::hash_map::Entry::Vacant(e) =
                                                    cur_cap.entry(g.dest.to_string())
                                                {
                                                    e.insert(off);
                                                    changed = true;
                                                }
                                            }
                                        } else if let Some(c) = base_ty.and_then(|v| self.reduce(v)) {
                                            changed |= insert_first(
                                                &mut cur,
                                                g.dest.to_string(),
                                                ValTy::Field { parent: c, offset_bits: off.saturating_mul(8) },
                                            );
                                        }
                                    }
                                }
                                Instruction::Load(l) => {
                                    if let Some(p) = operand_name(&l.address) {
                                        // Loading the env pointer out of an env slot.
                                        if env_slots.contains(&p) {
                                            changed |= insert_first(&mut cur, l.dest.to_string(), ValTy::EnvBase);
                                        } else {
                                            let nv = contents.get(&p).copied().or_else(|| {
                                                cur.get(&p).copied().and_then(|v| self.load_result(v))
                                            });
                                            if let Some(nv) = nv {
                                                changed |= insert_first(&mut cur, l.dest.to_string(), nv);
                                            }
                                            // loading the capture's stored pointer keeps the
                                            // capture instance identity (same env offset).
                                            if let Some(&off) = cur_cap.get(&p) {
                                                if let std::collections::hash_map::Entry::Vacant(e) =
                                                    cur_cap.entry(l.dest.to_string())
                                                {
                                                    e.insert(off);
                                                    changed = true;
                                                }
                                            }
                                        }
                                    }
                                }
                                Instruction::Store(s) => {
                                    if let (Some(src), Some(dst)) =
                                        (operand_name(&s.value), operand_name(&s.address))
                                    {
                                        // Storing the env pointer into an env slot marks the
                                        // stored value as the env base.
                                        if env_slots.contains(&dst) {
                                            changed |= insert_first(&mut cur, src.clone(), ValTy::EnvBase);
                                        }
                                        if let Some(v) = cur.get(&src).copied() {
                                            if let std::collections::hash_map::Entry::Vacant(e) =
                                                contents.entry(dst)
                                            {
                                                e.insert(v);
                                                changed = true;
                                            }
                                        }
                                    }
                                }
                                Instruction::BitCast(b) => {
                                    if let Some(n) = operand_name(&b.operand) {
                                        if let Some(x) = cur.get(&n).copied() {
                                            changed |= insert_first(&mut cur, b.dest.to_string(), x);
                                        }
                                        if let Some(&off) = cur_cap.get(&n) {
                                            if let std::collections::hash_map::Entry::Vacant(e) = cur_cap.entry(b.dest.to_string()) {
                                                e.insert(off);
                                                changed = true;
                                            }
                                        }
                                    }
                                }
                                Instruction::AddrSpaceCast(b) => {
                                    if let Some(x) = operand_name(&b.operand).and_then(|n| cur.get(&n).copied()) {
                                        changed |= insert_first(&mut cur, b.dest.to_string(), x);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }

                for (name, v) in &cur {
                    if let Some(tok) = self.render(*v) {
                        out.tokens.insert((fname.clone(), name.clone()), tok);
                    }
                }
                for (name, off) in &cur_cap {
                    out.captures.insert((fname.clone(), name.clone()), *off);
                }
            }
        }
        out
    }

    /// Number of composites recovered (for diagnostics / the producer summary line).
    pub fn composite_count(&self) -> usize {
        self.composites.len()
    }

    /// Number of (function, value) -> variable links recovered (for diagnostics).
    pub fn value_link_count(&self) -> usize {
        self.value_var.len()
    }

    /// Whether any debug-info types were recovered at all (gates the precision path).
    pub fn is_empty(&self) -> bool {
        self.composites.is_empty() && self.value_var.is_empty()
    }
}

// ---------------------------------------------------------------------------
// line-level parsing helpers
// ---------------------------------------------------------------------------

/// `!123 = <body>` -> `(123, "<body>")`.
fn parse_meta_line(line: &str) -> Option<(MetaId, &str)> {
    let rest = line.strip_prefix('!')?;
    let eq = rest.find(" = ")?;
    let id: MetaId = rest[..eq].parse().ok()?;
    Some((id, rest[eq + 3..].trim()))
}

/// `define ... @<name>(...` -> `<name>`.
fn parse_define_name(line: &str) -> Option<String> {
    let at = line.find('@')?;
    let rest = &line[at + 1..];
    let end = rest.find('(').unwrap_or(rest.len());
    Some(rest[..end].trim().to_string())
}

/// `#dbg_declare(ptr %v, !53, !DIExpression(...), ...)` or
/// `call void @llvm.dbg.declare(metadata ptr %v, metadata !53, metadata !DIExpression(...))`
/// -> `(value name without %, var id, env offset)`.
///
/// `env offset` is `Some(n)` when the DIExpression contains `DW_OP_deref` (the variable is a
/// coroutine/async capture at byte offset `n` -- `DW_OP_plus_uconst` -- inside the env the
/// value points at), and `None` for a plain declare (the variable is stored directly at the
/// value).
fn parse_dbg_declare(line: &str) -> Option<(String, MetaId, Option<u64>)> {
    let inner = if let Some(i) = line.find("#dbg_declare(") {
        &line[i + "#dbg_declare(".len()..]
    } else if let Some(i) = line.find("@llvm.dbg.declare(") {
        &line[i + "@llvm.dbg.declare(".len()..]
    } else {
        return None;
    };
    // first operand is `[metadata] ptr %NAME` (or just `%NAME`)
    let pct = inner.find('%')?;
    let after = &inner[pct + 1..];
    let end = after
        .find(|c: char| c == ',' || c == ')' || c.is_whitespace())
        .unwrap_or(after.len());
    let value = after[..end].to_string();
    // the variable metadata ref is the next `!<digits>` token
    let rest = &after[end..];
    let bang = rest.find('!')?;
    let after_bang = &rest[bang + 1..];
    let dend = after_bang.find(|c: char| !c.is_ascii_digit()).unwrap_or(after_bang.len());
    let var: MetaId = after_bang[..dend].parse().ok()?;
    // A DW_OP_deref in the DIExpression marks a capture; DW_OP_plus_uconst gives the offset.
    let env_off = line.find("DW_OP_deref").map(|_| {
        line.find("DW_OP_plus_uconst")
            .and_then(|i| {
                let tail = &line[i + "DW_OP_plus_uconst".len()..];
                let digits: String = tail
                    .trim_start_matches(|c: char| c == ',' || c == ' ')
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect();
                digits.parse().ok()
            })
            .unwrap_or(0)
    });
    Some((value, var, env_off))
}

/// Parse `!{ !a, !b, ... }` into the list of referenced ids.
fn parse_ref_list(body: &str) -> Vec<MetaId> {
    let mut out = Vec::new();
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'!' {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                if let Ok(n) = body[i + 1..j].parse() {
                    out.push(n);
                }
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

/// Return the raw value token following `key` (which must include its trailing `:`),
/// handling a quoted string or a bare token ended by `,` / `)`.
fn raw_field<'a>(body: &'a str, key: &str) -> Option<&'a str> {
    let idx = body.find(key)? + key.len();
    let rest = body[idx..].trim_start();
    if let Some(stripped) = rest.strip_prefix('"') {
        let end = stripped.find('"')?;
        Some(&stripped[..end])
    } else {
        let end = rest.find(|c: char| c == ',' || c == ')').unwrap_or(rest.len());
        Some(rest[..end].trim())
    }
}

/// Quoted string field, e.g. `name: "Resource"`.
fn str_field(body: &str, key: &str) -> Option<String> {
    raw_field(body, key).map(|s| s.to_string())
}

/// Integer field, e.g. `size: 128`.
fn num_field(body: &str, key: &str) -> Option<u64> {
    raw_field(body, key)?.parse().ok()
}

/// Metadata-reference field, e.g. `baseType: !214` -> `214`.
fn ref_field(body: &str, key: &str) -> Option<MetaId> {
    let v = raw_field(body, key)?;
    v.strip_prefix('!')?.parse().ok()
}

/// Bare identifier field, e.g. `tag: DW_TAG_member`.
fn ident_field(body: &str, key: &str) -> Option<String> {
    raw_field(body, key).map(|s| s.to_string())
}

/// The local SSA name of an operand (`%foo`), or `None` for constants/globals.
fn operand_name(op: &Operand) -> Option<String> {
    match op {
        Operand::LocalOperand { name, .. } => Some(name.to_string()),
        _ => None,
    }
}

/// Whether a GEP's source element type is a small integer, i.e. the opaque-pointer
/// byte-offset GEP shape (`getelementptr i8, ptr %p, i64 N`).
fn is_byte_gep(ty: &llvm_ir::TypeRef) -> bool {
    matches!(ty.as_ref(), Type::IntegerType { .. })
}

/// The constant byte offset of a GEP, from its single (or first) constant index operand.
fn gep_const_offset(indices: &[Operand]) -> Option<u64> {
    for op in indices {
        if let Operand::ConstantOperand(c) = op {
            if let Constant::Int { value, .. } = c.as_ref() {
                return Some(*value);
            }
        }
    }
    None
}

/// Insert only if the key is absent (SSA is single-assignment; first writer wins). Returns
/// whether an insert happened, so the propagation loop knows it made progress.
fn insert_first(map: &mut HashMap<String, ValTy>, k: String, v: ValTy) -> bool {
    if let std::collections::hash_map::Entry::Vacant(e) = map.entry(k) {
        e.insert(v);
        true
    } else {
        false
    }
}

/// Strip `.dbg.spill` (and a trailing `%`) so a dbg_declare value and a GEP base match.
fn strip_value_suffix(v: &str) -> &str {
    let v = v.strip_prefix('%').unwrap_or(v);
    v.strip_suffix(".dbg.spill").unwrap_or(v)
}

// ---------------------------------------------------------------------------
// tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// The exact shape captured from the real dominance-demo LLVM-19 IR
    /// (`dominance_demo_dbg.ll`): a `Resource { id: u64, data: u64 }` struct, a function
    /// `guarded(r: &Resource)`, and `main` with local `a: Resource`.
    const SNIPPET: &str = r#"
define internal void @_ZN14dominance_demo7guarded17habcdE(ptr %r) unnamed_addr #0 !dbg !417 {
start:
    #dbg_declare(ptr %r.dbg.spill, !430, !DIExpression(), !431)
    ret void
}

define internal void @_ZN14dominance_demo4main17ha21E() unnamed_addr #0 !dbg !472 {
start:
    #dbg_declare(ptr %a, !474, !DIExpression(), !484)
    #dbg_declare(ptr %b, !476, !DIExpression(), !485)
    ret void
}

!214 = !DIBasicType(name: "u64", size: 64, encoding: DW_ATE_unsigned)
!424 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&dominance_demo::Resource", baseType: !425, size: 64, align: 64, dwarfAddressSpace: 0)
!425 = !DICompositeType(tag: DW_TAG_structure_type, name: "Resource", scope: !420, file: !2, size: 128, align: 64, flags: DIFlagPublic, elements: !426, templateParams: !23, identifier: "7deb583bfbe57f8b93782909f65483f8")
!426 = !{!427, !428}
!427 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !425, file: !2, baseType: !214, size: 64, align: 64, flags: DIFlagPublic)
!428 = !DIDerivedType(tag: DW_TAG_member, name: "data", scope: !425, file: !2, baseType: !214, size: 64, align: 64, offset: 64, flags: DIFlagPublic)
!430 = !DILocalVariable(name: "r", arg: 1, scope: !418, file: !419, line: 6, type: !424)
!474 = !DILocalVariable(name: "a", scope: !475, file: !419, line: 30, type: !425, align: 8)
!476 = !DILocalVariable(name: "b", scope: !477, file: !419, line: 31, type: !425, align: 8)
"#;

    fn parsed() -> DebugTypes {
        DebugTypes::parse_str(SNIPPET)
    }

    #[test]
    fn recovers_struct_layout_with_offsets() {
        let dt = parsed();
        let layout = dt.struct_layout(425).expect("Resource composite");
        assert_eq!(layout.name, "Resource");
        assert_eq!(layout.size_bits, 128);
        assert_eq!(layout.members.len(), 2);
        assert_eq!(layout.members[0].name, "id");
        assert_eq!(layout.members[0].offset_bits, 0); // offset: absent -> 0
        assert_eq!(layout.members[0].size_bits, 64);
        assert_eq!(layout.members[1].name, "data");
        assert_eq!(layout.members[1].offset_bits, 64);
    }

    #[test]
    fn strips_pointer_to_composite() {
        let dt = parsed();
        // !424 is &Resource (pointer) -> should resolve to the Resource composite !425
        assert_eq!(dt.strip_to_composite(424), Some(425));
        // !425 is already the composite
        assert_eq!(dt.strip_to_composite(425), Some(425));
        // a basic type is not a composite
        assert_eq!(dt.strip_to_composite(214), None);
    }

    #[test]
    fn maps_parameter_value_to_composite() {
        let dt = parsed();
        // param `r` (declared as %r.dbg.spill) in guarded -> &Resource -> Resource
        let comp = dt
            .value_composite("_ZN14dominance_demo7guarded17habcdE", "r")
            .expect("r resolves to a composite");
        assert_eq!(comp, 425);
        // the .dbg.spill-suffixed name resolves the same way
        assert_eq!(
            dt.value_composite("_ZN14dominance_demo7guarded17habcdE", "r.dbg.spill"),
            Some(425)
        );
    }

    #[test]
    fn maps_local_value_to_composite() {
        let dt = parsed();
        // local `a: Resource` in main -> Resource directly (no pointer wrapper)
        assert_eq!(
            dt.value_composite("_ZN14dominance_demo4main17ha21E", "a"),
            Some(425)
        );
    }

    #[test]
    fn resolves_member_by_byte_offset() {
        let dt = parsed();
        // byte 0 -> id, byte 4 still within id (bits 0..64), byte 8 -> data
        assert_eq!(dt.resolve_member(425, 0).unwrap().name, "id");
        assert_eq!(dt.resolve_member(425, 4).unwrap().name, "id");
        assert_eq!(dt.resolve_member(425, 8).unwrap().name, "data");
        // byte 16 is past the struct -> no member
        assert!(dt.resolve_member(425, 16).is_none());
    }

    #[test]
    fn scoping_is_per_function() {
        let dt = parsed();
        // `a` exists only in main, not in guarded
        assert!(dt
            .value_composite("_ZN14dominance_demo7guarded17habcdE", "a")
            .is_none());
    }

    #[test]
    fn legacy_dbg_declare_call_form() {
        // older intrinsic form must parse too
        let ll = r#"
define void @f(ptr %p) !dbg !1 {
    call void @llvm.dbg.declare(metadata ptr %p, metadata !10, metadata !DIExpression())
    ret void
}
!5 = !DICompositeType(tag: DW_TAG_structure_type, name: "S", size: 64, elements: !6)
!6 = !{!7}
!7 = !DIDerivedType(tag: DW_TAG_member, name: "x", baseType: !8, size: 64)
!8 = !DIBasicType(name: "u64", size: 64, encoding: DW_ATE_unsigned)
!10 = !DILocalVariable(name: "p", arg: 1, type: !5)
"#;
        let dt = DebugTypes::parse_str(ll);
        assert_eq!(dt.value_composite("f", "p"), Some(5));
        assert_eq!(dt.resolve_member(5, 0).unwrap().name, "x");
    }

    #[test]
    fn value_type_name_returns_struct_name() {
        let dt = parsed();
        assert_eq!(
            dt.value_type_name("_ZN14dominance_demo7guarded17habcdE", "r"),
            Some("Resource")
        );
        assert_eq!(
            dt.value_type_name("_ZN14dominance_demo4main17ha21E", "a"),
            Some("Resource")
        );
    }

    #[test]
    fn parse_files_offsets_ids_without_collision() {
        // Two files that both use low metadata ids (!5, !6, !7, !8, !10) for DIFFERENT
        // structs. Merging must not alias them.
        let dir = std::env::temp_dir();
        let a = dir.join("afg_dbg_a.ll");
        let b = dir.join("afg_dbg_b.ll");
        let file_a = r#"
define void @fa(ptr %p) !dbg !1 {
    call void @llvm.dbg.declare(metadata ptr %p, metadata !10, metadata !DIExpression())
    ret void
}
!5 = !DICompositeType(tag: DW_TAG_structure_type, name: "Alpha", size: 64, elements: !6)
!6 = !{!7}
!7 = !DIDerivedType(tag: DW_TAG_member, name: "x", baseType: !8, size: 64)
!8 = !DIBasicType(name: "u64", size: 64, encoding: DW_ATE_unsigned)
!10 = !DILocalVariable(name: "p", arg: 1, type: !5)
"#;
        let file_b = r#"
define void @fb(ptr %q) !dbg !1 {
    call void @llvm.dbg.declare(metadata ptr %q, metadata !10, metadata !DIExpression())
    ret void
}
!5 = !DICompositeType(tag: DW_TAG_structure_type, name: "Beta", size: 64, elements: !6)
!6 = !{!7}
!7 = !DIDerivedType(tag: DW_TAG_member, name: "y", baseType: !8, size: 64)
!8 = !DIBasicType(name: "u64", size: 64, encoding: DW_ATE_unsigned)
!10 = !DILocalVariable(name: "q", arg: 1, type: !5)
"#;
        std::fs::write(&a, file_a).unwrap();
        std::fs::write(&b, file_b).unwrap();
        let dt = DebugTypes::parse_files([&a, &b]);
        // despite both files using !5 for their struct, the two resolve distinctly
        assert_eq!(dt.value_type_name("fa", "p"), Some("Alpha"));
        assert_eq!(dt.value_type_name("fb", "q"), Some("Beta"));
        let _ = std::fs::remove_file(&a);
        let _ = std::fs::remove_file(&b);
    }

    #[test]
    fn empty_without_debug_info() {
        let dt = DebugTypes::parse_str("define void @f() {\n  ret void\n}\n");
        assert!(dt.is_empty());
        assert_eq!(dt.composite_count(), 0);
    }

    /// The committed real-IR fixtures (compiled with rustc 1.85/1.86 -> LLVM-19,
    /// `-C debuginfo=2`), under `rail-rs/tests/fixtures/`. `AFG_*_LL` env vars override.
    fn fixture(env_var: &str, name: &str) -> String {
        std::env::var(env_var).unwrap_or_else(|_| {
            format!("{}/tests/fixtures/{}", env!("CARGO_MANIFEST_DIR"), name)
        })
    }

    /// Real-IR validation against the compiled dominance-demo LLVM-19 IR (pure text parse,
    /// no LLVM needed). Fixture committed under tests/fixtures; `AFG_DEMO_LL` overrides.
    #[test]
    fn real_demo_ir() {
        let path = fixture("AFG_DEMO_LL", "dominance_demo_dbg.ll");
        let dt = DebugTypes::parse_file(Path::new(&path));
        assert!(!dt.is_empty(), "no debug info recovered");
        eprintln!(
            "recovered {} composites, {} value->var links",
            dt.composite_count(),
            dt.value_link_count()
        );

        // Find the Resource composite by name (hash in the mangled fn name is unknown here).
        let resource = dt
            .composites
            .iter()
            .find(|(_, c)| c.name == "Resource")
            .map(|(id, _)| *id)
            .expect("Resource struct recovered from real IR");
        let layout = dt.struct_layout(resource).unwrap();
        eprintln!("Resource = {:?}", layout);
        assert_eq!(layout.members.len(), 2);
        assert_eq!(layout.members[0].name, "id");
        assert_eq!(layout.members[0].offset_bits, 0);
        assert_eq!(layout.members[1].name, "data");
        assert_eq!(layout.members[1].offset_bits, 64);

        // byte-offset resolution works on the real layout
        assert_eq!(dt.resolve_member(resource, 8).unwrap().name, "data");

        // at least one function parameter should resolve to Resource via dbg_declare
        let param_links = dt
            .value_var
            .keys()
            .filter(|(f, v)| {
                f.contains("dominance_demo")
                    && dt.value_composite(f, v) == Some(resource)
            })
            .count();
        eprintln!("{} value(s) resolve to Resource", param_links);
        assert!(param_links >= 1, "expected some value to resolve to Resource");
    }

    /// Real-IR validation of type propagation through temporaries, on the committed
    /// typegate-demo IR. Loads the module through `llvm-ir` (the crate already links LLVM);
    /// `AFG_TYPEGATE_LL` overrides the fixture path.
    #[test]
    fn real_propagation() {
        let path = fixture("AFG_TYPEGATE_LL", "typegate_demo_dbg.ll");
        let dt = DebugTypes::parse_file(Path::new(&path));
        let module = llvm_ir::Module::from_ir_path(&path).expect("parse IR");
        let vt = dt.propagate_types([&module]);
        // find the handler function (mangled name contains "handler")
        let handler = crate::util::normalize_function_name(
            &module
                .functions
                .iter()
                .find(|f| f.name.contains("7handler"))
                .expect("handler fn")
                .name,
        )
        .to_string();
        // %_4 = getelementptr i8, ptr %ctx, i64 8 is &ctx.cipher: a TEMPORARY that must
        // propagate to the Cipher type (the whole point: temporaries get typed).
        assert_eq!(
            vt.token(&handler, "%_4"),
            Some("Cipher"),
            "the GEP-result temporary must type to Cipher"
        );
        // %ctx itself (the &Ctx parameter) types to Ctx.
        assert_eq!(vt.token(&handler, "%ctx"), Some("Ctx"));
        eprintln!("propagated {} typed values", vt.len());
    }

    #[test]
    fn parse_dbg_declare_distinguishes_plain_and_env_captures() {
        // plain local
        assert_eq!(
            parse_dbg_declare("    #dbg_declare(ptr %a, !474, !DIExpression(), !484)"),
            Some(("a".to_string(), 474, None))
        );
        // coroutine capture at offset 0 (DW_OP_deref only)
        assert_eq!(
            parse_dbg_declare("    #dbg_declare(ptr %_1, !100, !DIExpression(DW_OP_deref), !61)"),
            Some(("_1".to_string(), 100, Some(0)))
        );
        // coroutine capture at a byte offset
        assert_eq!(
            parse_dbg_declare(
                "    #dbg_declare(ptr %_1, !101, !DIExpression(DW_OP_deref, DW_OP_plus_uconst, 864), !61)"
            ),
            Some(("_1".to_string(), 101, Some(864)))
        );
    }

    #[test]
    fn parse_str_populates_env_captures() {
        // An async-state-machine-shaped function: `%_1` is the env slot, with two captures
        // (a Cipher at offset 864 and an Org at offset 24).
        let ll = r#"
define void @coro(ptr %_1) !dbg !1 {
    #dbg_declare(ptr %_1, !10, !DIExpression(DW_OP_deref, DW_OP_plus_uconst, 864), !61)
    #dbg_declare(ptr %_1, !11, !DIExpression(DW_OP_deref, DW_OP_plus_uconst, 24), !61)
    ret void
}
!20 = !DICompositeType(tag: DW_TAG_structure_type, name: "Cipher", size: 64, elements: !21)
!21 = !{}
!22 = !DICompositeType(tag: DW_TAG_structure_type, name: "Org", size: 64, elements: !21)
!23 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !20, size: 64)
!24 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !22, size: 64)
!10 = !DILocalVariable(name: "cipher", type: !23)
!11 = !DILocalVariable(name: "org", type: !24)
"#;
        let dt = DebugTypes::parse_str(ll);
        // env slot recorded, and two captures with their offsets
        assert!(dt.env_slots.get("coro").unwrap().contains("%_1"));
        let caps = dt.captures.get("coro").unwrap();
        assert_eq!(caps.len(), 2);
        assert!(caps.contains(&(864, 10)));
        assert!(caps.contains(&(24, 11)));
        // and these are NOT treated as plain declares
        assert!(dt.dbg_decls.iter().all(|(f, _, _)| f != "coro"));
    }

    #[test]
    fn recovers_coroutine_capture_identity() {
        // In the complex async demo, get_cipher reloads the captured cipher at both the
        // is_accessible check and the to_json serve; both must resolve to the same env
        // capture offset so the dominance pass can bind them as one resource instance.
        let path = fixture("AFG_COMPLEX_LL", "complex_dbg.ll");
        let dt = DebugTypes::parse_file(Path::new(&path));
        let m = llvm_ir::Module::from_ir_path(&path).expect("parse complex fixture");
        let vt = dt.propagate_types([&m]);
        let gc = m
            .functions
            .iter()
            .find(|f| f.name.contains("10get_cipher28") && f.name.contains("closure"))
            .expect("get_cipher coroutine");
        let fname = crate::util::normalize_function_name(&gc.name).to_string();
        let mut by_off: HashMap<u64, usize> = HashMap::new();
        for ((f, _), off) in &vt.captures {
            if f == &fname {
                *by_off.entry(*off).or_default() += 1;
            }
        }
        assert!(
            by_off.values().any(|&c| c >= 2),
            "expected a captured resource reloaded at multiple sites (shared offset), got {by_off:?}"
        );
    }

    #[test]
    fn cycle_in_derived_chain_terminates() {
        // defensive: a pathological self-referential wrapper must not loop forever
        let ll = r#"
!1 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2)
!2 = !DIDerivedType(tag: DW_TAG_typedef, baseType: !1)
"#;
        let dt = DebugTypes::parse_str(ll);
        assert_eq!(dt.strip_to_composite(1), None);
    }
}
