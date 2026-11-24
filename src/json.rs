//! A tiny JSON writer, so tools can give agents machine-readable answers.

pub enum J {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

pub fn s(x: impl Into<String>) -> J {
    J::Str(x.into())
}

pub fn obj(fields: Vec<(&str, J)>) -> J {
    J::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

pub fn strs<I: IntoIterator<Item = String>>(xs: I) -> J {
    J::Arr(xs.into_iter().map(J::Str).collect())
}

fn esc(x: &str, out: &mut String) {
    out.push('"');
    for c in x.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

impl J {
    pub fn write(&self, out: &mut String) {
        match self {
            J::Null => out.push_str("null"),
            J::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            J::Num(n) => out.push_str(&n.to_string()),
            J::Str(x) => esc(x, out),
            J::Arr(xs) => {
                out.push('[');
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    x.write(out);
                }
                out.push(']');
            }
            J::Obj(fs) => {
                out.push('{');
                for (i, (k, v)) in fs.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    esc(k, out);
                    out.push(':');
                    v.write(out);
                }
                out.push('}');
            }
        }
    }
    pub fn to_line(&self) -> String {
        let mut out = String::new();
        self.write(&mut out);
        out.push('\n');
        out
    }
}
