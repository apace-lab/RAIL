use llvm_ir::Module;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

pub fn has_flag(args: &[String], flag: &str) -> bool {
    args.iter().any(|arg| arg == flag)
}

pub fn get_flag_value<'a>(args: &'a [String], flag_prefix: &str) -> Option<&'a str> {
    args.iter().find_map(|arg| arg.strip_prefix(flag_prefix))
}

pub fn write_module_to_file(module: &Module, output_txt: &str) -> Result<(), Box<dyn Error>> {
    let mut file = File::create(output_txt)?;

    writeln!(file, "=== Module ===")?;
    writeln!(file, "name: {}", module.name)?;
    writeln!(file, "source_file_name: {}", module.source_file_name)?;
    writeln!(file, "data_layout: {:?}", module.data_layout)?;
    writeln!(file, "target_triple: {:?}", module.target_triple)?;
    writeln!(file)?;

    writeln!(file, "=== Summary ===")?;
    writeln!(file, "defined functions: {}", module.functions.len())?;
    writeln!(
        file,
        "function declarations: {}",
        module.func_declarations.len()
    )?;
    writeln!(file, "global variables: {}", module.global_vars.len())?;
    writeln!(file, "global aliases: {}", module.global_aliases.len())?;
    writeln!(file, "global ifuncs: {}", module.global_ifuncs.len())?;
    writeln!(file)?;

    writeln!(file, "=== Function Declarations ===")?;
    for decl in &module.func_declarations {
        writeln!(file, "declare {}", decl.name)?;
        writeln!(file, "  return_type: {}", decl.return_type)?;
        writeln!(file, "  parameters:")?;

        for param in &decl.parameters {
            writeln!(file, "    {:?}", param)?;
        }

        writeln!(file)?;
    }

    writeln!(file, "=== Global Variables ===")?;
    for gv in &module.global_vars {
        writeln!(file, "{:?}", gv)?;
    }
    writeln!(file)?;

    writeln!(file, "=== Global Aliases ===")?;
    for alias in &module.global_aliases {
        writeln!(file, "{:?}", alias)?;
    }
    writeln!(file)?;

    writeln!(file, "=== Global IFuncs ===")?;
    for ifunc in &module.global_ifuncs {
        writeln!(file, "{:?}", ifunc)?;
    }
    writeln!(file)?;

    writeln!(file, "=== Defined Functions ===")?;
    for func in &module.functions {
        writeln!(file, "function: {}", func.name)?;
        writeln!(file, "  return_type: {}", func.return_type)?;
        writeln!(file, "  parameters:")?;

        for param in &func.parameters {
            writeln!(file, "    {:?}", param)?;
        }

        writeln!(file, "  basic_blocks: {}", func.basic_blocks.len())?;

        for block in &func.basic_blocks {
            writeln!(file, "  basic block: {}", block.name)?;
            writeln!(file, "    instructions:")?;

            for instr in &block.instrs {
                writeln!(file, "      {:?}", instr)?;
            }

            writeln!(file, "    terminator:")?;
            writeln!(file, "      {:?}", block.term)?;
        }

        writeln!(file)?;
    }

    Ok(())
}

pub fn resolve_signature_file(
    cli_path: Option<&str>,
    default_filename: &str,
    description: &str,
) -> Option<String> {
    // If user explicitly provided --api= or --ac=, use it.
    if let Some(path_str) = cli_path {
        let path = PathBuf::from(path_str);

        if path.is_file() {
            return Some(path.to_string_lossy().into_owned());
        }

        eprintln!(
            "[CRUX] error: provided {} does not exist: {}",
            description,
            path.display()
        );

        return None;
    }

    // Otherwise automatically look under:
    // <project_root>/signatures/
    let default_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("signatures")
        .join(default_filename);

    if default_path.is_file() {
        println!("[CRUX] found {}: {}", description, default_path.display());

        return Some(default_path.to_string_lossy().into_owned());
    }

    eprintln!(
        "[CRUX] error: cannot find {} at {}",
        description,
        default_path.display()
    );

    None
}

//////////////////////// analysis related ////////////////////////

/// direct_callee_name direct output: "%_ZN4main16spawn_user_query17h488fc5de2a3a0326E"
/// or @"_ZN4main16spawn_user_query28_$u7b$$u7b$closure$u7d$$u7d$17hb7b958eb69c4a9bcE"
/// but output from functions_by_name:
/// key = _ZN4main16spawn_user_query17h488fc5de2a3a0326E
/// func.name = _ZN4main16spawn_user_query17h488fc5de2a3a0326E
pub fn normalize_function_name(name: &str) -> &str {
    name.trim_start_matches('%')
        .trim_start_matches('@')
        .trim_matches('"')
}

pub fn normalize_block_label(name: &str) -> String {
    name.trim()
        .trim_start_matches('%')
        .trim_matches('"')
        .to_string()
}

/// check whether the block name is for abnormal executions
pub fn is_cleanup_block_name(name: &str) -> bool {
    name == "cleanup"
        || name.starts_with("cleanup.")
        || name.starts_with("cleanup")
        || name == "terminate"
        || name.starts_with("terminate")
        || name.starts_with("unreachable")
        || name == "panic"
        || name.starts_with("panic")
}
