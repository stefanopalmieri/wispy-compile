//! WispyScheme compiler CLI.
//!
//! Usage:
//!   cargo run -- --compile file.scm    # compile to Rust, print to stdout
//!
//! For interpreted execution and REPL, use wispy-vm:
//!   wispy file.scm                     # compile + run via Stak VM
//!   wispy-repl                         # interactive REPL with Cayley algebra

use wispy_scheme::compile;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let mut files = Vec::new();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--compile" => {} // compile mode is now the only mode
            arg if !arg.starts_with('-') => files.push(arg.to_string()),
            _ => {
                eprintln!("Usage: wispy [--compile] file.scm [file.scm ...]");
                eprintln!();
                eprintln!("Compiles Scheme to standalone Rust. For interpreted execution:");
                eprintln!("  wispy-vm:   wispy file.scm       (bytecode VM)");
                eprintln!("  wispy-repl: wispy-repl            (interactive REPL)");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    if files.is_empty() {
        eprintln!("Usage: wispy [--compile] file.scm [file.scm ...]");
        std::process::exit(1);
    }

    let mut src = String::new();
    for f in &files {
        src.push_str(&std::fs::read_to_string(f)
            .unwrap_or_else(|e| { eprintln!("{f}: {e}"); std::process::exit(1); }));
        src.push('\n');
    }
    print!("{}", compile::compile(&src));
}
