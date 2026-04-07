//! WispyScheme REPL and file runner.
//!
//! Usage:
//!   cargo run                          # REPL
//!   cargo run -- file.scm              # run a file
//!   cargo run -- -e '(+ 1 2)'         # evaluate expression
//!   cargo run -- --permissive file.scm # permissive mode (type errors return BOT)
//!   cargo run -- --compile file.scm    # compile to Rust, print to stdout

use wispy_scheme::eval::Eval;
use wispy_scheme::compile;

use std::io::{self, Write, BufRead};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let mut permissive = false;
    let mut compile_mode = false;
    let mut expr = None;
    let mut files = Vec::new();

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--strict" => {}  // now the default; accepted for backwards compat
            "--permissive" => permissive = true,
            "--compile" => compile_mode = true,
            "-e" => {
                i += 1;
                if i < args.len() {
                    expr = Some(args[i].clone());
                }
            }
            arg if !arg.starts_with('-') => files.push(arg.to_string()),
            _ => {
                eprintln!("Usage: wispy [--permissive] [--compile] [-e expr] [file.scm ...]");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    // Compile mode
    if compile_mode {
        if files.is_empty() {
            eprintln!("--compile requires a file argument");
            std::process::exit(1);
        }
        let mut src = String::new();
        for f in &files {
            src.push_str(&std::fs::read_to_string(f)
                .unwrap_or_else(|e| { eprintln!("{f}: {e}"); std::process::exit(1); }));
            src.push('\n');
        }
        print!("{}", compile::compile(&src));
        return;
    }

    // Evaluator — strict by default
    let mut ev = Eval::new();
    ev.strict = !permissive;

    // Evaluate expression from -e
    if let Some(src) = expr {
        let result = ev.eval_str(&src);
        ev.display(result);
        println!();
        return;
    }

    // Run files
    if !files.is_empty() {
        for f in &files {
            let src = std::fs::read_to_string(f)
                .unwrap_or_else(|e| { eprintln!("{f}: {e}"); std::process::exit(1); });
            ev.eval_str(&src);
        }
        return;
    }

    // REPL
    repl(&mut ev);
}

fn repl(ev: &mut Eval) {
    use std::panic::{catch_unwind, AssertUnwindSafe, set_hook};

    // Suppress default panic output in the REPL; we handle errors ourselves
    set_hook(Box::new(|_| {}));

    println!("WispyScheme v0.1.0");
    println!("Type (permissive-mode) to silence type errors, (strict-mode) to restore.");
    println!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        print!("wispy> ");
        stdout.flush().unwrap();

        let mut line = String::new();
        if stdin.lock().read_line(&mut line).unwrap() == 0 {
            println!();
            break; // EOF
        }

        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        // Handle multi-line input: count parens
        let mut input = line.to_string();
        while !balanced(&input) {
            print!("  ...  ");
            stdout.flush().unwrap();
            let mut cont = String::new();
            if stdin.lock().read_line(&mut cont).unwrap() == 0 {
                break;
            }
            input.push(' ');
            input.push_str(cont.trim());
        }

        // Catch panics (type errors, unbound variables, etc.) so the REPL continues
        let result = catch_unwind(AssertUnwindSafe(|| {
            ev.eval_str(&input)
        }));

        match result {
            Ok(val) => {
                if val != ev.void_val {
                    ev.display(val);
                    println!();
                }
            }
            Err(payload) => {
                let msg = if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = payload.downcast_ref::<&str>() {
                    s.to_string()
                } else {
                    "unknown error".to_string()
                };
                eprintln!("error: {msg}");
            }
        }
    }
}

fn balanced(s: &str) -> bool {
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escape = false;

    for c in s.chars() {
        if escape {
            escape = false;
            continue;
        }
        if in_string {
            if c == '\\' { escape = true; }
            else if c == '"' { in_string = false; }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            ';' => break, // comment, stop counting
            _ => {}
        }
    }
    depth <= 0 && !in_string
}
