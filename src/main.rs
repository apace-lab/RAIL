use llvm_ir::Module;
use std::env;
use std::error::Error;

use rail_rs::util;
use rail_rs::{CrossModuleAnalysis, ModuleAnalysis};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage:");
        eprintln!(
            "  {} <input.ll> [output.txt] [llm_catalog.json] [ac_catalog.json]",
            args[0]
        );
        std::process::exit(1);
    }

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("default")).init();

    // positional args (not starting with "--") are input .ll paths; accept one or many.
    // multiple inputs are analyzed together as a cross-module program (e.g. a crate's
    // lib + bin, where `main` is in the bin but most code is in the lib).
    let inputs: Vec<&String> = args[1..].iter().filter(|a| !a.starts_with("--")).collect();
    if inputs.is_empty() {
        eprintln!("Usage:");
        eprintln!(
            "  {} <input.ll> [more.ll ...] [--pag=<mode>] [--k=N] [--api=..] [--ac=..] [--info] [--cfg] [--cg]",
            args[0]
        );
        std::process::exit(1);
    }

    let mut modules: Vec<Module> = Vec::with_capacity(inputs.len());
    for input_ll in &inputs {
        let module = Module::from_ir_path(input_ll)
            .map_err(|e| format!("failed to parse LLVM IR file {}: {}", input_ll, e))?;
        println!("Parsed LLVM IR from: {}", input_ll);
        modules.push(module);
    }

    // optionally write the parsed module(s) for debugging
    if util::has_flag(&args, "--info") {
        for (i, module) in modules.iter().enumerate() {
            let output_txt = match modules.len() {
                1 => "parsed_module.txt".to_string(),
                _ => format!("parsed_module_{i}.txt"),
            };
            util::write_module_to_file(module, &output_txt)?;
            println!("Wrote parsed module info to: {}", output_txt);
        }
    }

    // print cfg for each function, per module: default from llvm-ir
    if util::has_flag(&args, "--cfg") {
        let mut file = std::fs::File::create("cfg.txt")?;
        for module in &modules {
            let analysis = ModuleAnalysis::new(module);
            for func in &module.functions {
                let fn_analysis = analysis.fn_analysis(&func.name);
                fn_analysis
                    .control_flow_graph()
                    .print_cfg(&func.name, &mut file)?;
            }
        }
        println!("Wrote control flow graph to cfg.txt");
    }

    // cross-module analysis over all input modules (works for a single module too)
    let mut analysis = CrossModuleAnalysis::new(modules.iter());

    // print cg (cross-module): default from llvm-ir
    if util::has_flag(&args, "--cg") {
        let _ = analysis.call_graph().print_call_graph();
        println!("Wrote call graph to cg.txt");
    }

    // generate pag (records context points during the analysis if catalogs were set)
    if let Some(mode) = util::get_flag_value(&args, "--pag=") {
        let k = util::get_flag_value(&args, "--k=");
        match mode {
            "kcfa" | "kobj" | "kmix" => {
                // must have k
                if k.is_none() {
                    eprintln!("PAG mode {} requires --k=<number>", mode);
                    std::process::exit(1);
                }

                let k_size: Option<usize> = k.map(|value| {
                    value
                        .parse::<usize>()
                        .expect("--k must be a non-negative integer")
                });

                let pag: std::cell::Ref<'_, rail_rs::PointerAssignmentGraph<'_>> =
                    analysis.pointer_assignment_graph(mode, k_size);
                pag.print_pointer_assignment_graph()?;
            }

            "afg" => {
                // load context catalogs if both are given, so the analysis records context points
                let llm_api_path_cli = util::get_flag_value(&args, "--api=");
                let ac_path_cli = util::get_flag_value(&args, "--ac=");

                let llm_api_path = util::resolve_signature_file(
                    llm_api_path_cli.as_deref(),
                    "llm_api_functions.json",
                    "LLM API signature file",
                );

                let ac_path = util::resolve_signature_file(
                    ac_path_cli.as_deref(),
                    "ac_functions.json",
                    "access-control signature file",
                );

                if let (Some(llm_api_path), Some(ac_path)) = (llm_api_path, ac_path) {
                    let llm_api =
                        rail_rs::signature::load_signatures(std::path::Path::new(&llm_api_path))?;
                    let ac = rail_rs::signature::load_signatures(std::path::Path::new(&ac_path))?;

                    println!(
                        "Loaded {} LLM API and {} AC signatures",
                        llm_api.len(),
                        ac.len()
                    );

                    analysis.set_context_catalogs(llm_api, ac);

                    let pag: std::cell::Ref<'_, rail_rs::PointerAssignmentGraph<'_>> =
                        analysis.pointer_assignment_graph(mode, None);
                    pag.print_pointer_assignment_graph()?;

                    // // run the taint analysis on the PAG
                    // let afg = analysis.taint_analysis(mode, None);
                    // afg.print_leak_result(false, false);
                } else {
                    eprintln!("Usage: cargo run -- input.ll --api=api.json --ac=ac.json");
                    return Ok(());
                }
            }

            _ => {
                // default
                let pag: std::cell::Ref<'_, rail_rs::PointerAssignmentGraph<'_>> =
                    analysis.pointer_assignment_graph(mode, None);
                pag.print_pointer_assignment_graph()?;
            }
        }

        println!("Wrote pointer assignment graph to pag.txt");
    }

    Ok(())
}
