//! Indentation-aware lexer.

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Int(i64),
    Sym(&'static str),
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
    pub start: usize, // byte offset
    pub end: usize,
}

const SYMS: &[&str] = &[
    "<=>", "..", "=>", "!=", "<=", ">=", ":", ",", "(", ")", "[", "]", ".", "=", "<", ">", "+", "-",
    "*", "|",
];

pub fn lex(src: &str) -> Result<Vec<Token>, (usize, String)> {
    let mut out: Vec<Token> = Vec::new();
    let mut indents: Vec<usize> = vec![0];
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut line = 1;
    let mut depth: i32 = 0; // bracket depth
    let mut at_line_start = true;
    let mut continuing = false; // previous line ended with a continuation token

    while i < bytes.len() {
        if at_line_start {
            // measure indentation
            let mut col = 0;
            let mut j = i;
            while j < bytes.len() && (bytes[j] == b' ' || bytes[j] == b'\t') {
                col += if bytes[j] == b'\t' { 4 } else { 1 };
                j += 1;
            }
            // blank or comment-only line
            if j >= bytes.len() || bytes[j] == b'\n' || bytes[j] == b'#' || bytes[j] == b'\r' {
                while j < bytes.len() && bytes[j] != b'\n' {
                    j += 1;
                }
                if j < bytes.len() {
                    j += 1;
                    line += 1;
                }
                i = j;
                continue;
            }
            i = j;
            at_line_start = false;
            if depth == 0 && !continuing {
                let cur = *indents.last().unwrap();
                if col > cur {
                    indents.push(col);
                    out.push(Token { tok: Tok::Indent, line, start: i, end: i });
                } else {
                    while col < *indents.last().unwrap() {
                        indents.pop();
                        out.push(Token { tok: Tok::Dedent, line, start: i, end: i });
                    }
                    if col != *indents.last().unwrap() {
                        return Err((line, "inconsistent indentation".into()));
                    }
                }
            }
            continuing = false;
        }
        let c = bytes[i];
        if c == b'\n' {
            line += 1;
            i += 1;
            at_line_start = true;
            if depth > 0 {
                continue;
            }
            // continuation if the line ended with a binary-ish token
            let cont = match out.last().map(|t| &t.tok) {
                Some(Tok::Sym(s)) => matches!(*s, "," | "=>" | "<=>" | "=" | "+" | "-" | "|"),
                Some(Tok::Ident(s)) => matches!(s.as_str(), "in" | "and" | "or"),
                _ => false,
            };
            if cont {
                continuing = true;
            } else if !matches!(out.last().map(|t| &t.tok), Some(Tok::Newline) | None) {
                out.push(Token { tok: Tok::Newline, line: line - 1, start: i, end: i });
            }
            continue;
        }
        if c == b' ' || c == b'\t' || c == b'\r' {
            i += 1;
            continue;
        }
        if c == b'#' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if c.is_ascii_digit() {
            let s = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let n: i64 = src[s..i].parse().map_err(|_| (line, "bad number".to_string()))?;
            out.push(Token { tok: Tok::Int(n), line, start: s, end: i });
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' || c >= 0x80 {
            let s = i;
            while i < bytes.len() {
                let d = bytes[i];
                if d.is_ascii_alphanumeric() || d == b'_' || d >= 0x80 {
                    i += 1;
                } else if d == b'#' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
                    i += 1; // segment marker, e.g. Ada#2
                } else {
                    break;
                }
            }
            out.push(Token { tok: Tok::Ident(src[s..i].to_string()), line, start: s, end: i });
            continue;
        }
        let mut matched = false;
        for s in SYMS {
            if src[i..].starts_with(s) {
                if *s == "(" || *s == "[" {
                    depth += 1;
                }
                if *s == ")" || *s == "]" {
                    depth -= 1;
                }
                out.push(Token { tok: Tok::Sym(s), line, start: i, end: i + s.len() });
                i += s.len();
                matched = true;
                break;
            }
        }
        if !matched {
            return Err((line, format!("unexpected character '{}'", src[i..].chars().next().unwrap())));
        }
    }
    if !matches!(out.last().map(|t| &t.tok), Some(Tok::Newline) | None) {
        out.push(Token { tok: Tok::Newline, line, start: i, end: i });
    }
    while indents.len() > 1 {
        indents.pop();
        out.push(Token { tok: Tok::Dedent, line, start: i, end: i });
    }
    out.push(Token { tok: Tok::Eof, line, start: i, end: i });
    Ok(out)
}
