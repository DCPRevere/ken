//! Runs every example and every failure case through the ken binary.

use std::path::Path;
use std::process::Command;

fn run(path: &Path) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_ken")).arg("check").arg(path).output().expect("run ken");
    (out.status.success(), String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr))
}

#[test]
fn examples_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().map(|x| x == "ken") != Some(true) {
            continue;
        }
        let (ok, out) = run(&p);
        if p.file_name().unwrap() == "bootstrap.ken" {
            assert!(!ok && out.contains("bootstrap paradox"), "{}:\n{}", p.display(), out);
        } else {
            assert!(ok && out.contains(" 0 failed"), "{}:\n{}", p.display(), out);
        }
    }
}

#[test]
fn failures_are_caught() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fail");
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        let src = std::fs::read_to_string(&p).unwrap();
        let first = src.lines().next().unwrap_or("");
        let (ok, out) = run(&p);
        if first.starts_with("# expect-ok") {
            assert!(ok && out.contains(" 0 failed"), "{} should pass:\n{}", p.display(), out);
        } else {
            let want = first.trim_start_matches("# expect-error:").trim();
            assert!(!ok, "{} should fail:\n{}", p.display(), out);
            assert!(out.contains(want), "{}: wanted `{}` in:\n{}", p.display(), want, out);
        }
    }
}

#[test]
fn blue_eyes_other_sizes() {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/blue_eyes.ken");
    for (n, b) in [(1, 1), (3, 1), (4, 2), (6, 4), (7, 7)] {
        let out = Command::new(env!("CARGO_BIN_EXE_ken")).arg("check").arg(&p).arg("--given").arg(format!("n={},b={}", n, b)).output().unwrap();
        let s = String::from_utf8_lossy(&out.stdout);
        assert!(out.status.success() && s.contains(" 0 failed"), "n={} b={}:\n{}", n, b, s);
    }
}

fn output(path: &Path, engine: &str, given: &str) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_ken"))
        .args(["check", "-q", "--engine", engine, "--given", given])
        .arg(path)
        .output()
        .unwrap();
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// The symbolic engine must agree exactly with the explicit one.
#[test]
fn engines_agree() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let files = ["tests/fail/blue_eyes_scale.ken", "examples/blue_eyes.ken", "examples/blue_eyes_no_guru.ken", "tests/fail/blue_eyes_nights.ken", "tests/fail/blue_eyes_too_early.ken"];
    for f in files {
        let p = root.join(f);
        for n in 1..=7 {
            for b in 0..=n {
                let g = format!("n={},b={}", n, b);
                let x = output(&p, "explicit", &g);
                let s = output(&p, "symbolic", &g);
                assert_eq!(x, s, "{} with {}: engines disagree", f, g);
            }
        }
    }
}

fn run_with(path: &Path, given: &str, envs: &[(&str, &str)]) -> (bool, String) {
    let mut c = Command::new(env!("CARGO_BIN_EXE_ken"));
    c.args(["check", "-q", "--engine", "symbolic", "--given", given]).arg(path);
    for (k, v) in envs {
        c.env(k, v);
    }
    let out = c.output().unwrap();
    (out.status.success(), String::from_utf8_lossy(&out.stdout).to_string())
}

/// Exact Blue Eyes behaviour at sizes far beyond the explicit engine.
#[test]
fn blue_eyes_at_scale() {
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fail/blue_eyes_scale.ken");
    for (n, b) in [(50, 1), (50, 2), (50, 50), (120, 37), (200, 1), (200, 100), (200, 199), (200, 200)] {
        let (ok, out) = run_with(&p, &format!("n={},b={}", n, b), &[]);
        assert!(ok && out.contains(" 0 failed"), "n={} b={}:\n{}", n, b, out);
    }
}

/// The symbolic shortcuts must agree with the general symbolic path.
#[test]
fn shortcuts_agree_with_general_path() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for f in ["tests/fail/blue_eyes_scale.ken", "examples/blue_eyes_no_guru.ken", "tests/fail/blue_eyes_too_early.ken"] {
        let p = root.join(f);
        for (n, b) in [(9, 0), (12, 1), (12, 5), (16, 16), (24, 9), (30, 15)] {
            let g = format!("n={},b={}", n, b);
            let fast = run_with(&p, &g, &[]);
            let slow = run_with(&p, &g, &[("KEN_NO_SHORTCUTS", "1")]);
            assert_eq!(fast, slow, "{} with {}", f, g);
        }
    }
}
