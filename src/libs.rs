//! Libraries: `use space`, `use "lib/court.ken" as court`.
//!
//! A library is a file of types, facts, actions, rules and invariants. It can't
//! declare agents, timelines or worlds. Its names are reached through its alias
//! (`space.go`); names it doesn't declare are left for the user's model to supply
//! (`space` uses the model's `Place`). Libraries are spliced into the worlds that
//! use them, with every name they declare prefixed by the alias.

use crate::ast::*;
use crate::lexer;
use crate::parser;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub const SPACE: &str = include_str!("lib/space.ken");

fn builtin(name: &str) -> Option<&'static str> {
    match name {
        "space" => Some(SPACE),
        _ => None,
    }
}

pub struct Loader {
    /// all source text, so spans stay printable
    pub full: String,
    /// libraries being loaded, to catch cycles: (identity, name to show)
    stack: Vec<(String, String)>,
    /// types a library leaves for the model to declare: (library, type)
    requires: Vec<(String, String)>,
}

impl Loader {
    pub fn new(full: String) -> Self {
        Loader { full, stack: vec![], requires: vec![] }
    }

    /// Resolve the `use` lines of the main file: top-level ones become shared library
    /// declarations; those inside a world are spliced into that world.
    pub fn resolve(&mut self, decls: Vec<Decl>, dir: &Path) -> Result<(Vec<Decl>, Vec<Decl>), String> {
        let mut libs = vec![];
        let mut out = vec![];
        for d in decls {
            match d {
                Decl::Use { target, alias, span } => libs.extend(self.use_lib(&target, alias, dir, "", span.line)?),
                Decl::World { name, about, revises, decls, span } => {
                    let mut inner = vec![];
                    for d in decls {
                        match d {
                            Decl::Use { target, alias, span } => inner.extend(self.use_lib(&target, alias, dir, "", span.line)?),
                            other => inner.push(other),
                        }
                    }
                    out.push(Decl::World { name, about, revises, decls: inner, span });
                }
                other => out.push(other),
            }
        }
        // types the libraries expect the model to declare
        let mut have: HashSet<String> = HashSet::new();
        let note = |ds: &[Decl], have: &mut HashSet<String>| {
            for d in ds {
                match d {
                    Decl::Type { name, .. } => {
                        have.insert(name.clone());
                    }
                    Decl::Agent { names, .. } => {
                        for n in names {
                            if n.range.is_some() {
                                have.insert(n.base.clone());
                            }
                        }
                    }
                    _ => {}
                }
            }
        };
        note(&out, &mut have);
        for d in &out {
            if let Decl::World { decls, .. } = d {
                note(decls, &mut have);
            }
        }
        for (lib, ty) in &self.requires {
            if !have.contains(ty) {
                return Err(format!("library {} needs your model to declare `type {}`", lib, ty));
            }
        }
        Ok((out, libs))
    }

    fn use_lib(&mut self, target: &UseTarget, alias: Option<String>, dir: &Path, prefix: &str, line: usize) -> Result<Vec<Decl>, String> {
        let at = |m: String| if line > 0 { format!("line {}: {}", line, m) } else { m };
        let (text, id, shown, lib_dir, base) = match target {
            UseTarget::Builtin(n) if n == "std" => return Err(at("`std` is always there; it doesn't need `use`".into())),
            UseTarget::Builtin(n) => {
                let t = builtin(n).ok_or_else(|| at(format!("no library called '{}' (built in: space). For a file, write `use \"{}.ken\"`", n, n)))?;
                (t.to_string(), n.clone(), n.clone(), dir.to_path_buf(), n.clone())
            }
            UseTarget::Path(p) => {
                let path = dir.join(p);
                let t = std::fs::read_to_string(&path).map_err(|e| at(format!("can't read library {}: {}", path.display(), e)))?;
                let canon = path.canonicalize().unwrap_or(path.clone()).display().to_string();
                (t, canon, p.clone(), path.parent().map(Path::to_path_buf).unwrap_or_else(|| PathBuf::from(".")), parser::alias_of_path(p))
            }
        };
        let alias = alias.unwrap_or(base);
        if self.stack.iter().any(|(i, _)| *i == id) {
            let names: Vec<&str> = self.stack.iter().map(|(_, n)| n.as_str()).collect();
            return Err(at(format!("libraries use each other in a circle: {} → {}", names.join(" → "), shown)));
        }
        self.stack.push((id.clone(), shown.clone()));
        let r = self.load(&text, &shown, &lib_dir, &format!("{}{}.", prefix, alias));
        self.stack.pop();
        let mut decls = r?;
        let lib_name = match target {
            UseTarget::Builtin(n) => n.clone(),
            UseTarget::Path(_) => id,
        };
        decls.insert(0, Decl::Used { lib: lib_name, alias: format!("{}{}", prefix, alias) });
        Ok(decls)
    }

    /// Parse a library and prefix the names it declares.
    fn load(&mut self, text: &str, id: &str, dir: &Path, prefix: &str) -> Result<Vec<Decl>, String> {
        self.full.push('\n');
        let off = self.full.len();
        self.full.push_str(text);
        let mut toks = lexer::lex(text).map_err(|(l, m)| format!("{}:{}: {}", id, l, m))?;
        for t in toks.iter_mut() {
            t.start += off;
            t.end += off;
        }
        let aliases = parser::scan_aliases(&toks);
        let saved_aliases = parser::ALIASES.with(|a| std::mem::replace(&mut *a.borrow_mut(), aliases.clone()));
        let saved_worlds = parser::WORLD_NAMES.with(|w| std::mem::take(&mut *w.borrow_mut()));
        let parsed = {
            let mut p = parser::Parser::new(toks, &self.full);
            p.parse_file()
        };
        parser::ALIASES.with(|a| *a.borrow_mut() = saved_aliases);
        parser::WORLD_NAMES.with(|w| *w.borrow_mut() = saved_worlds);
        let decls = parsed.map_err(|(l, m)| format!("{}:{}: {}", id, l, m))?;

        let mut out = vec![];
        let mut own = vec![];
        for d in decls {
            match d {
                Decl::Use { target, alias, span } => out.extend(self.use_lib(&target, alias, dir, prefix, 0).map_err(|m| if m.contains("in a circle") { m } else { format!("{}:{}: {}", id, span.line, m) })?),
                Decl::Type { .. } | Decl::Fact { .. } | Decl::Action { .. } | Decl::Rule { .. } | Decl::Expect(_) => own.push(d),
                Decl::Agent { span, .. } | Decl::Segment { span, .. } => return Err(format!("{}:{}: a library can't declare agents; the model that uses it does", id, span.line)),
                Decl::World { span, .. } => return Err(format!("{}:{}: a library can't declare worlds", id, span.line)),
                Decl::Timeline(_) => return Err(format!("{}: a library can't have a timeline", id)),
                Decl::Given(_) | Decl::TimeTravel(..) | Decl::AllowBootstrap | Decl::Used { .. } => return Err(format!("{}: a library can only declare types, facts, actions, rules and invariants", id)),
            }
        }
        // the names this library declares
        let mut declared: HashSet<String> = HashSet::new();
        for d in &own {
            match d {
                Decl::Type { name, def, .. } => {
                    declared.insert(name.clone());
                    if let TypeDef::Enum(vs) = def {
                        declared.extend(vs.iter().cloned());
                    }
                }
                Decl::Fact { name, .. } | Decl::Action { name, .. } => {
                    declared.insert(name.clone());
                }
                _ => {}
            }
        }
        // types used but not declared here: the model must supply them
        let builtin_ty = ["bool", "Bool", "Int", "int", "Agent"];
        let mut free: Vec<String> = vec![];
        let mut want = |t: &TypeRef| {
            if let TypeRef::Named(n) = t {
                if !declared.contains(n) && !builtin_ty.contains(&n.as_str()) && !n.contains('.') && !free.contains(n) {
                    free.push(n.clone());
                }
            }
        };
        for d in &own {
            match d {
                Decl::Fact { params, ty, .. } => {
                    params.iter().for_each(&mut want);
                    want(ty);
                }
                Decl::Action { params, .. } => params.iter().filter_map(|(_, t)| t.as_ref()).for_each(&mut want),
                Decl::Type { def: TypeDef::Record(fs), .. } => fs.iter().for_each(|(_, t)| want(t)),
                _ => {}
            }
        }
        self.requires.extend(free.into_iter().map(|t| (id.to_string(), t)));
        let r = Renamer { prefix: prefix.to_string(), declared, inner: aliases };
        out.extend(own.iter().map(|d| r.decl(d)));
        Ok(out)
    }
}

/// Prefixes the names a library declares (and the names of the libraries it uses).
struct Renamer {
    prefix: String,
    declared: HashSet<String>,
    inner: Vec<String>,
}

impl Renamer {
    fn name(&self, n: &str, bound: &[String]) -> String {
        if bound.iter().any(|b| b == n) {
            return n.to_string();
        }
        let inner = n.split_once('.').map(|(a, _)| self.inner.iter().any(|x| x == a)).unwrap_or(false);
        if self.declared.contains(n) || inner {
            format!("{}{}", self.prefix, n)
        } else {
            n.to_string()
        }
    }

    fn span(&self, s: Span) -> Span {
        // library lines don't refer to the user's file
        Span { line: 0, ..s }
    }

    fn ty(&self, t: &TypeRef, bound: &[String]) -> TypeRef {
        match t {
            TypeRef::Named(n) => TypeRef::Named(self.name(n, bound)),
            TypeRef::Range(a, b) => TypeRef::Range(self.expr(a, bound), self.expr(b, bound)),
        }
    }

    fn call(&self, c: &Call, bound: &[String]) -> Call {
        Call { name: self.name(&c.name, bound), args: c.args.iter().map(|a| self.expr(a, bound)).collect(), span: self.span(c.span) }
    }

    fn expr(&self, e: &E, bound: &[String]) -> E {
        use ExprKind::*;
        let r = |x: &E| self.expr(x, bound);
        let kind = match &e.kind {
            Int(n) => Int(*n),
            Bool(b) => Bool(*b),
            Name(n) => Name(self.name(n, bound)),
            Qualified(w, n) => Qualified(w.clone(), n.clone()),
            Call(n, args) => Call(self.name(n, bound), args.iter().map(r).collect()),
            Index(g, i) => Index(g.clone(), r(i)),
            Field(b, f) => Field(r(b), f.clone()),
            Tuple(xs) => Tuple(xs.iter().map(r).collect()),
            Not(x) => Not(r(x)),
            Neg(x) => Neg(r(x)),
            Bin(op, a, b) => Bin(*op, r(a), r(b)),
            Quant { all, var, ty, body } => {
                let mut b2 = bound.to_vec();
                b2.push(var.clone());
                Quant { all: *all, var: var.clone(), ty: self.ty(ty, bound), body: self.expr(body, &b2) }
            }
            Epistemic { agent, mode, body } => Epistemic { agent: r(agent), mode: *mode, body: r(body) },
            Common { group, body } => Common { group: group.clone(), body: r(body) },
            Deducible { agent, body } => Deducible { agent: r(agent), body: r(body) },
            Possible { agent, body } => Possible { agent: r(agent), body: r(body) },
            Saw { agent, what } => Saw { agent: r(agent), what: r(what) },
            At(x, t) => At(r(x), t.clone()),
            SeenAs { event, by } => SeenAs { event: r(event), by: r(by) },
            Wants { agent, body } => Wants { agent: r(agent), body: r(body) },
            Suspects { agent, body } => Suspects { agent: r(agent), body: r(body) },
        };
        Rc::new(Expr { kind, span: self.span(e.span) })
    }

    fn assign(&self, a: &Assign, bound: &[String]) -> Assign {
        let mut b2 = bound.to_vec();
        if let Some((v, _, _)) = &a.for_range {
            b2.push(v.clone());
        }
        Assign {
            target: self.expr(&a.target, &b2),
            value: self.expr(&a.value, &b2),
            for_range: a.for_range.as_ref().map(|(v, lo, hi)| (v.clone(), self.expr(lo, bound), self.expr(hi, bound))),
            span: self.span(a.span),
        }
    }

    fn seen(&self, items: &[SeenItem], bound: &[String]) -> Vec<SeenItem> {
        items
            .iter()
            .map(|it| {
                let mut b2 = bound.to_vec();
                let who = match &it.who {
                    Who::Everyone => Who::Everyone,
                    Who::Nobody => Who::Nobody,
                    Who::Agent(e) => Who::Agent(self.expr(e, bound)),
                    Who::Every { ty, var, cond } => {
                        b2.push(var.clone());
                        Who::Every { ty: ty.as_ref().map(|t| self.name(t, bound)), var: var.clone(), cond: cond.as_ref().map(|c| self.expr(c, &b2)) }
                    }
                };
                let mods = it
                    .mods
                    .iter()
                    .map(|m| match m {
                        Modifier::As(cs) => Modifier::As(cs.iter().map(|c| self.call(c, &b2)).collect()),
                        Modifier::Hiding(e) => Modifier::Hiding(self.expr(e, &b2)),
                        Modifier::Secretly(xs) => Modifier::Secretly(xs.iter().map(|x| self.expr(x, &b2)).collect()),
                    })
                    .collect();
                SeenItem { who, mods }
            })
            .collect()
    }

    fn decl(&self, d: &Decl) -> Decl {
        let none: Vec<String> = vec![];
        match d {
            Decl::Type { name, def, span } => Decl::Type {
                name: self.name(name, &none),
                def: match def {
                    TypeDef::Enum(vs) => TypeDef::Enum(vs.iter().map(|v| self.name(v, &none)).collect()),
                    TypeDef::Range(a, b) => TypeDef::Range(self.expr(a, &none), self.expr(b, &none)),
                    TypeDef::Record(fs) => TypeDef::Record(fs.iter().map(|(f, t)| (f.clone(), self.ty(t, &none))).collect()),
                },
                span: self.span(*span),
            },
            Decl::Fact { name, params, ty, default, domain, span } => Decl::Fact {
                name: self.name(name, &none),
                params: params.iter().map(|t| self.ty(t, &none)).collect(),
                ty: self.ty(ty, &none),
                default: default.as_ref().map(|e| self.expr(e, &none)),
                domain: domain.as_ref().map(|vs| vs.iter().map(|e| self.expr(e, &none)).collect()),
                span: self.span(*span),
            },
            Decl::Action { name, params, needs, effects, seen_by, unseen, span } => {
                let bound: Vec<String> = params.iter().map(|(p, _)| p.clone()).collect();
                Decl::Action {
                    name: self.name(name, &none),
                    params: params.iter().map(|(p, t)| (p.clone(), t.as_ref().map(|t| self.ty(t, &none)))).collect(),
                    needs: needs.iter().map(|e| self.expr(e, &bound)).collect(),
                    effects: effects.iter().map(|a| self.assign(a, &bound)).collect(),
                    seen_by: seen_by.as_ref().map(|s| self.seen(s, &bound)),
                    unseen: *unseen,
                    span: self.span(*span),
                }
            }
            Decl::Rule { name, private, trigger, for_every, when, then, span } => {
                // pattern variables: names in the trigger that the library doesn't declare
                let pat = match trigger {
                    Trigger::After(c) | Trigger::AfterSees(_, c) => c,
                };
                let mut bound: Vec<String> = pat.args.iter().filter_map(|a| if let ExprKind::Name(n) = &a.kind { if self.declared.contains(n) { None } else { Some(n.clone()) } } else { None }).collect();
                if let Some((_, v)) = for_every {
                    bound.push(v.clone());
                }
                Decl::Rule {
                    name: format!("{}{}", self.prefix, name),
                    private: *private,
                    trigger: match trigger {
                        Trigger::After(c) => Trigger::After(self.call(c, &bound)),
                        Trigger::AfterSees(a, c) => Trigger::AfterSees(self.expr(a, &bound), self.call(c, &bound)),
                    },
                    for_every: for_every.as_ref().map(|(t, v)| (self.name(t, &none), v.clone())),
                    when: when.as_ref().map(|e| self.expr(e, &bound)),
                    then: match then {
                        RuleThen::Do(c) => RuleThen::Do(self.call(c, &bound)),
                        RuleThen::Concludes(a, f) => RuleThen::Concludes(self.expr(a, &bound), self.expr(f, &bound)),
                    },
                    span: self.span(*span),
                }
            }
            Decl::Expect(e) => Decl::Expect(Expect { time: e.time.clone(), formulas: e.formulas.iter().map(|f| self.expr(f, &none)).collect(), span: self.span(e.span) }),
            other => other.clone(),
        }
    }
}
