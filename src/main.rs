//! Ken: worlds, agents, events and beliefs, with a consistency checker.

mod ast;
mod bdd;
mod check;
mod engine;
mod eval;
mod foreign;
mod kripke;
mod lexer;
mod parser;
mod state;
mod symbolic;
mod value;
mod world;

use state::Level;
use std::collections::HashMap;
use std::process::ExitCode;

pub fn load(file: &str, src: &str, given: &HashMap<String, i64>) -> Result<world::Program, String> {
    let toks = lexer::lex(src).map_err(|(l, m)| format!("{}:{}: {}", file, l, m))?;
    parser::WORLD_NAMES.with(|w| *w.borrow_mut() = parser::scan_world_names(&toks));
    let mut p = parser::Parser::new(toks, src);
    let decls = p.parse_file().map_err(|(l, m)| format!("{}:{}: {}", file, l, m))?;
    // the prelude's text is appended to the source so its spans stay printable
    let full = format!("{}\n{}", src, world::PRELUDE);
    let offset = src.len() + 1;
    let mut ptoks = lexer::lex(world::PRELUDE).map_err(|(l, m)| format!("prelude:{}: {}", l, m))?;
    for t in ptoks.iter_mut() {
        t.start += offset;
        t.end += offset;
        t.line = 0;
    }
    let mut pp = parser::Parser::new(ptoks, &full);
    let prelude = pp.parse_file().map_err(|(l, m)| format!("prelude:{}: {}", l, m))?;
    world::compile(file, &full, decls, prelude, given).map_err(|(l, m)| if l > 0 { format!("{}:{}: {}", file, l, m) } else { format!("{}: {}", file, m) })
}

fn usage() -> ExitCode {
    eprintln!("usage: ken check <file.ken> [--given name=value,...] [--engine auto|explicit|symbolic] [--quiet]");
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--version" || a == "-V") {
        println!("ken {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    let mut it = args.iter().peekable();
    if it.peek().map(|s| s.as_str()) == Some("check") {
        it.next();
    }
    let mut file = None;
    let mut given = HashMap::new();
    let mut quiet = false;
    let mut engine = check::Engine::Auto;
    while let Some(a) = it.next() {
        match a.as_str() {
            "--given" => {
                let Some(v) = it.next() else { return usage() };
                for kv in v.split(',') {
                    let Some((k, v)) = kv.split_once('=') else { return usage() };
                    let Ok(n) = v.trim().parse::<i64>() else { return usage() };
                    given.insert(k.trim().to_string(), n);
                }
            }
            "--quiet" | "-q" => quiet = true,
            "--engine" => {
                engine = match it.next().map(|s| s.as_str()) {
                    Some("auto") => check::Engine::Auto,
                    Some("explicit") => check::Engine::Explicit,
                    Some("symbolic") => check::Engine::Symbolic,
                    _ => return usage(),
                }
            }
            "-h" | "--help" => return usage(),
            f if file.is_none() => file = Some(f.to_string()),
            _ => return usage(),
        }
    }
    let Some(file) = file else { return usage() };
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {}", file, e);
            return ExitCode::from(2);
        }
    };
    let prog = match load(&file, &src, &given) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {}", e);
            return ExitCode::from(1);
        }
    };
    let checker = check::Checker::new(&prog, engine);
    let report = checker.check();
    let mut errors = 0;
    let mut warnings = 0;
    let multi = prog.worlds.len() > 1;
    for d in &report.diags {
        let tag = match d.level {
            Level::Error => {
                errors += 1;
                "error"
            }
            Level::Warning => {
                warnings += 1;
                "warning"
            }
            Level::Note => "note",
        };
        if quiet && d.level == Level::Note {
            continue;
        }
        let place = match (&d.at, multi) {
            (Some(at), true) => format!(" [{} @ {}]", d.world, at),
            (Some(at), false) => format!(" [@ {}]", at),
            (None, true) => format!(" [{}]", d.world),
            (None, false) => String::new(),
        };
        let loc = if d.line > 0 { format!("{}:{}", file, d.line) } else { file.clone() };
        println!("{} {}{}: {}", tag, loc, place, d.msg);
    }
    println!(
        "{}: {} expectation(s) hold, {} failed; {} error(s), {} warning(s)",
        file, report.passed, report.failed, errors, warnings
    );
    if errors > 0 { ExitCode::from(1) } else { ExitCode::SUCCESS }
}
