//! WispyScheme compiler CLI.
//!
//! Usage:
//!   cargo run -- --compile file.scm              # compile to Rust (no GC)
//!   cargo run -- --gc cheney --compile file.scm  # compile with Cheney GC
//!
//! For interpreted execution and REPL, use wispy-vm:
//!   wispy file.scm                     # compile + run via Stak VM
//!   wispy-repl                         # interactive REPL with Cayley algebra

use wispy_scheme::compile;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let mut files = Vec::new();
    let mut gc_mode = compile::GcMode::None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--compile" => {} // compile mode is now the only mode
            "--gc" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("--gc requires an argument: none, cheney");
                    std::process::exit(1);
                }
                gc_mode = match args[i].as_str() {
                    "none" => compile::GcMode::None,
                    "cheney" => compile::GcMode::Cheney,
                    other => {
                        eprintln!("Unknown GC mode: {other} (use: none, cheney)");
                        std::process::exit(1);
                    }
                };
            }
            arg if !arg.starts_with('-') => files.push(arg.to_string()),
            _ => {
                eprintln!("Usage: wispy [--gc none|cheney] [--compile] file.scm");
                eprintln!();
                eprintln!("Options:");
                eprintln!("  --gc none    Grow-only heap, no GC (default)");
                eprintln!("  --gc cheney  Semi-space Cheney copying collector");
                eprintln!();
                eprintln!("For interpreted execution:");
                eprintln!("  wispy-vm:   wispy file.scm       (bytecode VM)");
                eprintln!("  wispy-repl: wispy-repl            (interactive REPL)");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    if files.is_empty() {
        eprintln!("Usage: wispy [--gc none|cheney] [--compile] file.scm");
        std::process::exit(1);
    }

    let mut src = String::new();
    for f in &files {
        src.push_str(&std::fs::read_to_string(f)
            .unwrap_or_else(|e| { eprintln!("{f}: {e}"); std::process::exit(1); }));
        src.push('\n');
    }
    print!("{}", compile::compile_with_options(&src, gc_mode));
}
