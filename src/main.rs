//! Ken: worlds, agents, events and beliefs, with a consistency checker.

mod ast;
mod bdd;
mod check;
mod engine;
mod eval;
mod foreign;
mod json;
mod kripke;
mod lexer;
mod libs;
mod mind;
mod parser;
mod state;
mod symbolic;
mod tools;
mod value;
mod world;

use state::Level;
use std::collections::HashMap;
use std::process::ExitCode;

pub fn load(file: &str, src: &str, given: &HashMap<String, i64>) -> Result<world::Program, String> {
    load_with(file, src, given, &[]).map(|(p, _)| p)
}

/// Load a program, plus extra formulas (questions) parsed in its context.
pub fn load_with(
    file: &str,
    src: &str,
    given: &HashMap<String, i64>,
    queries: &[String],
) -> Result<(world::Program, Vec<ast::E>), String> {
    let toks = lexer::lex(src).map_err(|(l, m)| format!("{}:{}: {}", file, l, m))?;
    parser::WORLD_NAMES.with(|w| *w.borrow_mut() = parser::scan_world_names(&toks));
    let aliases = parser::scan_aliases(&toks);
    parser::ALIASES.with(|a| *a.borrow_mut() = aliases.clone());
    let mut p = parser::Parser::new(toks, src);
    let decls = p
        .parse_file()
        .map_err(|(l, m)| format!("{}:{}: {}", file, l, m))?;
    // the prelude's and the questions' text is appended to the source so spans stay printable
    let full = format!("{}\n{}", src, world::PRELUDE);
    let offset = src.len() + 1;
    let mut ptoks = lexer::lex(world::PRELUDE).map_err(|(l, m)| format!("prelude:{}: {}", l, m))?;
    for t in ptoks.iter_mut() {
        t.start += offset;
        t.end += offset;
        t.line = 0;
    }
    let prelude = {
        let mut pp = parser::Parser::new(ptoks, &full);
        pp.parse_file()
            .map_err(|(l, m)| format!("prelude:{}: {}", l, m))?
    };
    // libraries
    let dir = std::path::Path::new(file).parent().map(|d| d.to_path_buf()).unwrap_or_default();
    let mut loader = libs::Loader::new(full);
    let (decls, lib_decls) = loader.resolve(decls, &dir).map_err(|m| format!("{}: {}", file, m))?;
    let mut full = loader.full;
    parser::ALIASES.with(|a| *a.borrow_mut() = aliases.clone());
    let mut qs = vec![];
    for q in queries {
        full.push('\n');
        let off = full.len();
        full.push_str(q);
        let mut qt = lexer::lex(q).map_err(|(_, m)| format!("in `{}`: {}", q, m))?;
        for t in qt.iter_mut() {
            t.start += off;
            t.end += off;
            t.line = 0;
        }
        let mut qp = parser::Parser::new(qt, &full);
        let e = qp.expr().map_err(|(_, m)| format!("in `{}`: {}", q, m))?;
        qp.end_of_input()
            .map_err(|(_, m)| format!("in `{}`: {}", q, m))?;
        qs.push(e);
    }
    let prog = world::compile(file, &full, decls, prelude, lib_decls, given).map_err(|(l, m)| {
        if l > 0 {
            format!("{}:{}: {}", file, l, m)
        } else {
            format!("{}: {}", file, m)
        }
    })?;
    Ok((prog, qs))
}

const USAGE: &str = "usage:
  ken check    FILE [options]                 check a story
  ken why      FILE EVENT \"A believes …\"      why someone believes something then
  ken who      FILE EVENT \"…\"                 who knows, believes, or could work it out
  ken whatif   FILE --drop EVENT              what changes if an event never happened
  ken whatif   FILE --move EVENT --after EVENT
  ken suggest  FILE                           events that would fix failing expectations
  ken timeline FILE [--html OUT.html]         who believes what, step by step
  ken mind     FILE AGENT [--at EVENT]        what one person knows, believes, suspects
                                              and wants at each step
options: --given name=value,...  --engine auto|explicit|symbolic  --quiet  --world NAME
         --json   machine-readable output (one JSON object on stdout), for agents";

fn usage() -> ExitCode {
    eprintln!("{}", USAGE);
    ExitCode::from(2)
}

struct Opts {
    cmd: String,
    pos: Vec<String>,
    given: HashMap<String, i64>,
    quiet: bool,
    engine: check::Engine,
    world: Option<String>,
    html: Option<String>,
    drop: Option<String>,
    mv: Option<String>,
    after: Option<String>,
    max: usize,
    json: bool,
    at: Option<String>,
}

fn parse_args(args: &[String]) -> Result<Opts, ()> {
    let mut it = args.iter().peekable();
    let cmds = ["check", "why", "who", "whatif", "suggest", "timeline", "mind"];
    let cmd = match it.peek().map(|s| s.as_str()) {
        Some(c) if cmds.contains(&c) => {
            it.next();
            c.to_string()
        }
        _ => "check".into(),
    };
    let mut o = Opts {
        cmd,
        pos: vec![],
        given: HashMap::new(),
        quiet: false,
        engine: check::Engine::Auto,
        world: None,
        html: None,
        drop: None,
        mv: None,
        after: None,
        max: 5,
        json: false,
        at: None,
    };
    while let Some(a) = it.next() {
        match a.as_str() {
            "--given" => {
                let v = it.next().ok_or(())?;
                for kv in v.split(',') {
                    let (k, v) = kv.split_once('=').ok_or(())?;
                    let n = v.trim().parse::<i64>().map_err(|_| ())?;
                    o.given.insert(k.trim().to_string(), n);
                }
            }
            "--quiet" | "-q" => o.quiet = true,
            "--engine" => {
                o.engine = match it.next().map(|s| s.as_str()) {
                    Some("auto") => check::Engine::Auto,
                    Some("explicit") => check::Engine::Explicit,
                    Some("symbolic") => check::Engine::Symbolic,
                    _ => return Err(()),
                }
            }
            "--world" => o.world = Some(it.next().ok_or(())?.clone()),
            "--html" => o.html = Some(it.next().ok_or(())?.clone()),
            "--drop" => o.drop = Some(it.next().ok_or(())?.clone()),
            "--move" => o.mv = Some(it.next().ok_or(())?.clone()),
            "--after" => o.after = Some(it.next().ok_or(())?.clone()),
            "--json" => o.json = true,
            "--at" => o.at = Some(it.next().ok_or(())?.clone()),
            "--max" => o.max = it.next().ok_or(())?.parse().map_err(|_| ())?,
            "-h" | "--help" => return Err(()),
            p => o.pos.push(p.to_string()),
        }
    }
    Ok(o)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--version" || a == "-V") {
        println!("ken {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    let Ok(o) = parse_args(&args) else {
        return usage();
    };
    let Some(file) = o.pos.first().cloned() else {
        return usage();
    };
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            if o.json {
                print!("{}", json::obj(vec![("error", json::s(format!("{}: {}", file, e)))]).to_line());
            } else {
                eprintln!("{}: {}", file, e);
            }
            return ExitCode::from(2);
        }
    };
    let result = match o.cmd.as_str() {
        "check" => return run_check(&file, &src, &o),
        "why" | "who" => ask(&file, &src, &o),
        "whatif" => {
            tools::parse_change(o.drop.clone(), o.mv.clone(), o.after.clone()).and_then(|c| {
                let given = o.given.clone();
                let f = file.clone();
                tools::whatif(&move |s: &str| load(&f, s, &given), &src, o.engine, &c)
            })
        }
        "suggest" => {
            let given = o.given.clone();
            let f = file.clone();
            tools::suggest(&move |s: &str| load(&f, s, &given), &src, o.engine, o.max)
        }
        "timeline" => timeline(&file, &src, &o),
        "mind" => mind_cmd(&file, &src, &o),
        _ => return usage(),
    };
    // commands that build their own JSON say so by starting with '{'
    match result {
        Ok(text) if o.json && !text.starts_with('{') => {
            print!("{}", json::obj(vec![("text", json::s(text))]).to_line());
            ExitCode::SUCCESS
        }
        Ok(text) => {
            print!("{}", text);
            ExitCode::SUCCESS
        }
        Err(e) if o.json => {
            print!("{}", json::obj(vec![("error", json::s(e))]).to_line());
            ExitCode::from(1)
        }
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::from(1)
        }
    }
}

fn ask(file: &str, src: &str, o: &Opts) -> Result<String, String> {
    if o.pos.len() != 3 {
        return Err(format!(
            "`ken {}` needs a file, an event and a formula in quotes",
            o.cmd
        ));
    }
    let (prog, qs) = load_with(file, src, &o.given, &[o.pos[2].clone()])?;
    let spec = match &o.world {
        Some(w) if !o.pos[1].contains('.') => format!("{}.{}", w, o.pos[1]),
        _ => o.pos[1].clone(),
    };
    let (wid, step) = tools::find_step(&prog, &spec)?;
    // `why` needs the history that only the explicit engine keeps
    let engine = if o.cmd == "why" {
        check::Engine::Explicit
    } else {
        o.engine
    };
    let checker = check::Checker::new(&prog, engine);
    checker.check();
    if o.cmd == "why" {
        tools::why(&prog, &checker, wid, step, &qs[0])
    } else {
        tools::who(&prog, &checker, wid, step, &qs[0])
    }
}

fn timeline(file: &str, src: &str, o: &Opts) -> Result<String, String> {
    let prog = load(file, src, &o.given)?;
    let only = match &o.world {
        Some(w) => Some(prog.world_by_name(w).ok_or(format!("no world '{}'", w))?),
        None => None,
    };
    let checker = check::Checker::new(&prog, check::Engine::Explicit);
    checker.check();
    let grids = tools::timeline(&prog, &checker, only);
    if o.json {
        return Ok(json::obj(vec![("facts", tools::timeline_json(&grids))]).to_line());
    }
    match &o.html {
        Some(out) => {
            std::fs::write(out, tools::timeline_html(file, &grids))
                .map_err(|e| format!("{}: {}", out, e))?;
            Ok(format!("wrote {}\n", out))
        }
        None => Ok(tools::timeline_text(&grids)),
    }
}

fn mind_cmd(file: &str, src: &str, o: &Opts) -> Result<String, String> {
    if o.pos.len() != 2 {
        return Err("`ken mind` needs a file and an agent, e.g. `ken mind story.ken Ann`".into());
    }
    let prog = load(file, src, &o.given)?;
    let m = mind::mind(&prog, file, &o.pos[1], o.world.as_deref())?;
    let at = match &o.at {
        Some(l) => Some(
            m.steps
                .iter()
                .position(|s| &s.label == l)
                .ok_or(format!("no event '{}' in world '{}'", l, m.world))?,
        ),
        None => None,
    };
    Ok(if o.json {
        mind::json(&m, at).to_line()
    } else {
        mind::text(&m, at)
    })
}

fn run_check(file: &str, src: &str, o: &Opts) -> ExitCode {
    let prog = match load(file, src, &o.given) {
        Ok(p) => p,
        Err(e) => {
            if o.json {
                print!("{}", json::obj(vec![("error", json::s(e))]).to_line());
            } else {
                eprintln!("error: {}", e);
            }
            return ExitCode::from(1);
        }
    };
    let checker = check::Checker::new(&prog, o.engine);
    let report = checker.check();
    let mut errors = 0;
    let mut warnings = 0;
    let multi = prog.worlds.len() > 1;
    if o.json {
        let mut ds = vec![];
        for d in &report.diags {
            match d.level {
                Level::Error => errors += 1,
                Level::Warning => warnings += 1,
                Level::Note => {}
            }
            if o.quiet && d.level == Level::Note {
                continue;
            }
            ds.push(json::obj(vec![
                (
                    "level",
                    json::s(match d.level {
                        Level::Error => "error",
                        Level::Warning => "warning",
                        Level::Note => "note",
                    }),
                ),
                ("line", json::J::Num(d.line as i64)),
                ("world", json::s(d.world.clone())),
                ("at", d.at.clone().map(json::J::Str).unwrap_or(json::J::Null)),
                ("message", json::s(d.msg.clone())),
            ]));
        }
        let out = json::obj(vec![
            ("file", json::s(file)),
            ("ok", json::J::Bool(errors == 0 && report.failed == 0)),
            ("passed", json::J::Num(report.passed as i64)),
            ("failed", json::J::Num(report.failed as i64)),
            ("errors", json::J::Num(errors as i64)),
            ("warnings", json::J::Num(warnings as i64)),
            ("diagnostics", json::J::Arr(ds)),
        ]);
        print!("{}", out.to_line());
        return if errors > 0 { ExitCode::from(1) } else { ExitCode::SUCCESS };
    }
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
        if o.quiet && d.level == Level::Note {
            continue;
        }
        let place = match (&d.at, multi) {
            (Some(at), true) => format!(" [{} @ {}]", d.world, at),
            (Some(at), false) => format!(" [@ {}]", at),
            (None, true) => format!(" [{}]", d.world),
            (None, false) => String::new(),
        };
        let loc = if d.line > 0 {
            format!("{}:{}", file, d.line)
        } else {
            file.to_string()
        };
        println!("{} {}{}: {}", tag, loc, place, d.msg);
    }
    println!(
        "{}: {} expectation(s) hold, {} failed; {} error(s), {} warning(s)",
        file, report.passed, report.failed, errors, warnings
    );
    if errors > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
