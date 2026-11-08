//! Recursive-descent parser for Ken.

use crate::ast::*;
use crate::lexer::{Tok, Token};
use std::rc::Rc;

pub struct Parser<'a> {
    toks: Vec<Token>,
    pos: usize,
    #[allow(dead_code)]
    pub src: &'a str,
}

pub type PResult<T> = Result<T, (usize, String)>;

const RESERVED: &[&str] = &[
    "and", "or", "not", "knows", "believes", "saw", "at", "as", "in", "for", "because", "despite",
    "then", "where", "hiding", "secretly", "whether", "concludes", "seen", "by", "all", "some",
    "common", "deducible", "possible", "before", "do", "when", "after", "sees", "every",
];

impl<'a> Parser<'a> {
    pub fn new(toks: Vec<Token>, src: &'a str) -> Self {
        Parser { toks, pos: 0, src }
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, k: usize) -> &Tok {
        let i = (self.pos + k).min(self.toks.len() - 1);
        &self.toks[i].tok
    }
    fn line(&self) -> usize {
        self.toks[self.pos].line
    }
    fn start(&self) -> usize {
        self.toks[self.pos].start
    }
    fn prev_end(&self) -> usize {
        if self.pos == 0 { 0 } else { self.toks[self.pos - 1].end }
    }
    fn advance(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }
    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        let found = match self.peek() {
            Tok::Ident(s) => format!("'{}'", s),
            Tok::Int(n) => format!("'{}'", n),
            Tok::Sym(s) => format!("'{}'", s),
            Tok::Newline => "end of line".into(),
            Tok::Indent => "an indented block".into(),
            Tok::Dedent => "end of block".into(),
            Tok::Eof => "end of file".into(),
        };
        Err((self.line(), format!("{} (found {})", msg.into(), found)))
    }
    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s == kw)
    }
    fn is_kw_at(&self, k: usize, kw: &str) -> bool {
        matches!(self.peek_at(k), Tok::Ident(s) if s == kw)
    }
    fn is_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(x) if *x == s)
    }
    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn eat_sym(&mut self, s: &str) -> bool {
        if self.is_sym(s) {
            self.advance();
            true
        } else {
            false
        }
    }
    fn expect_kw(&mut self, kw: &str) -> PResult<()> {
        if self.eat_kw(kw) { Ok(()) } else { self.err(format!("expected '{}'", kw)) }
    }
    fn expect_sym(&mut self, s: &str) -> PResult<()> {
        if self.eat_sym(s) { Ok(()) } else { self.err(format!("expected '{}'", s)) }
    }
    fn ident(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.advance();
                Ok(s)
            }
            _ => self.err("expected a name"),
        }
    }
    fn label(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.advance();
                Ok(s)
            }
            Tok::Int(n) => {
                self.advance();
                Ok(n.to_string())
            }
            _ => self.err("expected an event name"),
        }
    }
    fn newline(&mut self) -> PResult<()> {
        match self.peek() {
            Tok::Newline => {
                self.advance();
                Ok(())
            }
            Tok::Eof | Tok::Dedent => Ok(()),
            _ => self.err("expected end of line"),
        }
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.advance();
        }
    }
    fn mk(&self, kind: ExprKind, start: usize, line: usize) -> E {
        Rc::new(Expr { kind, span: Span { line, start, end: self.prev_end() } })
    }

    // ---------------------------------------------------------------- file

    pub fn parse_file(&mut self) -> PResult<Vec<Decl>> {
        let mut decls = Vec::new();
        self.skip_newlines();
        while !matches!(self.peek(), Tok::Eof) {
            decls.push(self.decl()?);
            self.skip_newlines();
        }
        Ok(decls)
    }

    fn block<T>(&mut self, mut item: impl FnMut(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut out = Vec::new();
        self.skip_newlines();
        if !matches!(self.peek(), Tok::Indent) {
            return self.err("expected an indented block");
        }
        self.advance();
        loop {
            self.skip_newlines();
            if matches!(self.peek(), Tok::Dedent) {
                self.advance();
                break;
            }
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            out.push(item(self)?);
        }
        Ok(out)
    }

    fn span_from(&self, start: usize, line: usize) -> Span {
        Span { line, start, end: self.prev_end() }
    }

    fn decl(&mut self) -> PResult<Decl> {
        let start = self.start();
        let line = self.line();
        let kw = match self.peek().clone() {
            Tok::Ident(s) => s,
            _ => return self.err("expected a declaration"),
        };
        match kw.as_str() {
            "world" => {
                self.advance();
                let name = self.ident()?;
                let mut about = Vec::new();
                let mut revises = None;
                if self.eat_kw("about") {
                    about.push(self.ident()?);
                    while self.eat_sym(",") {
                        about.push(self.ident()?);
                    }
                }
                if self.eat_kw("revises") {
                    let w = self.ident()?;
                    self.expect_kw("from")?;
                    let t = self.time_ref()?;
                    revises = Some((w, t));
                }
                self.newline()?;
                let decls = self.block(|p| p.decl())?;
                Ok(Decl::World { name, about, revises, decls, span: self.span_from(start, line) })
            }
            "given" => {
                self.advance();
                let mut items = Vec::new();
                loop {
                    let n = self.ident()?;
                    let v = if self.eat_sym("=") { Some(self.expr()?) } else { None };
                    items.push((n, v));
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.newline()?;
                Ok(Decl::Given(items))
            }
            "agent" => {
                self.advance();
                // segment form: agent Ada#2 is Loop1.Ada at e3
                if self.is_kw_at(1, "is") {
                    let name = self.ident()?;
                    self.expect_kw("is")?;
                    let first = self.ident()?;
                    let (origin_world, origin) = if self.eat_sym(".") {
                        (Some(first), self.ident()?)
                    } else {
                        (None, first)
                    };
                    self.expect_kw("at")?;
                    let at = self.time_ref()?;
                    self.newline()?;
                    return Ok(Decl::Segment { name, origin_world, origin, at, span: self.span_from(start, line) });
                }
                let mut names = Vec::new();
                loop {
                    let base = self.ident()?;
                    let range = if self.eat_sym("[") {
                        let lo = self.expr()?;
                        self.expect_sym("..")?;
                        let hi = self.expr()?;
                        self.expect_sym("]")?;
                        Some((lo, hi))
                    } else {
                        None
                    };
                    names.push(AgentName { base, range });
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                let mut mode = None;
                if self.eat_sym(":") {
                    let m = self.ident()?;
                    mode = Some(match m.as_str() {
                        "logician" => Mode::Logician,
                        "person" => Mode::Person,
                        _ => return Err((line, format!("unknown reasoning mode '{}': use person or logician", m))),
                    });
                }
                let mut sees_all_of = None;
                if self.eat_kw("sees") {
                    self.expect_kw("all")?;
                    self.expect_kw("of")?;
                    sees_all_of = Some(self.ident()?);
                }
                self.newline()?;
                Ok(Decl::Agent { names, mode, sees_all_of, span: self.span_from(start, line) })
            }
            "type" => {
                self.advance();
                let name = self.ident()?;
                self.expect_sym("=")?;
                let def = if self.eat_sym("(") {
                    let mut fields = Vec::new();
                    loop {
                        let f = self.ident()?;
                        self.expect_sym(":")?;
                        let t = self.type_ref()?;
                        fields.push((f, t));
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                    self.expect_sym(")")?;
                    TypeDef::Record(fields)
                } else if matches!(self.peek(), Tok::Int(_)) || self.is_sym("-") {
                    let lo = self.additive()?;
                    self.expect_sym("..")?;
                    let hi = self.additive()?;
                    TypeDef::Range(lo, hi)
                } else {
                    let mut vs = vec![self.ident()?];
                    while self.eat_sym("|") {
                        vs.push(self.ident()?);
                    }
                    TypeDef::Enum(vs)
                };
                self.newline()?;
                Ok(Decl::Type { name, def, span: self.span_from(start, line) })
            }
            "fact" => {
                self.advance();
                let name = self.ident()?;
                let mut params = Vec::new();
                if self.eat_sym("(") {
                    loop {
                        params.push(self.type_ref()?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                    self.expect_sym(")")?;
                }
                self.expect_sym(":")?;
                let ty = self.type_ref()?;
                let mut default = None;
                let mut domain = None;
                if self.eat_sym("=") {
                    default = Some(self.expr()?);
                }
                if self.eat_kw("in") {
                    let mut vs = vec![self.expr()?];
                    while self.eat_sym(",") {
                        vs.push(self.expr()?);
                    }
                    domain = Some(vs);
                }
                self.newline()?;
                Ok(Decl::Fact { name, params, ty, default, domain, span: self.span_from(start, line) })
            }
            "action" => {
                self.advance();
                let name = self.ident()?;
                let mut params = Vec::new();
                self.expect_sym("(")?;
                if !self.is_sym(")") {
                    loop {
                        let p = self.ident()?;
                        let t = if self.eat_sym(":") { Some(self.type_ref()?) } else { None };
                        params.push((p, t));
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                }
                self.expect_sym(")")?;
                self.newline()?;
                let mut needs = Vec::new();
                let mut effects = Vec::new();
                let mut seen_by = None;
                if matches!(self.peek(), Tok::Indent) {
                    let clauses = self.block(|p| p.action_clause())?;
                    for c in clauses {
                        match c {
                            ActionClause::Needs(e) => needs.push(e),
                            ActionClause::Effect(a) => effects.extend(a),
                            ActionClause::SeenBy(s) => seen_by = Some(s),
                        }
                    }
                }
                Ok(Decl::Action { name, params, needs, effects, seen_by, span: self.span_from(start, line) })
            }
            "private" | "rule" => {
                let private = self.eat_kw("private");
                self.expect_kw("rule")?;
                let name = self.ident()?;
                self.expect_sym(":")?;
                self.newline()?;
                // body: after <trigger>[, for every T v]:  when <cond>:  do/concludes
                let mut out: Option<Decl> = None;
                let items = self.block(|p| {
                    let start = p.start();
                    let line = p.line();
                    p.expect_kw("after")?;
                    let trigger = if matches!(p.peek_at(1), Tok::Ident(s) if s == "sees") {
                        let a = p.primary()?;
                        p.expect_kw("sees")?;
                        Trigger::AfterSees(a, p.call()?)
                    } else {
                        Trigger::After(p.call()?)
                    };
                    let mut for_every = None;
                    if p.eat_sym(",") {
                        p.expect_kw("for")?;
                        p.expect_kw("every")?;
                        let t = p.ident()?;
                        let v = p.ident()?;
                        for_every = Some((t, v));
                    }
                    p.expect_sym(":")?;
                    p.newline()?;
                    let inner = p.block(|p| {
                        let mut when = None;
                        if p.eat_kw("when") {
                            when = Some(p.expr()?);
                            p.expect_sym(":")?;
                            p.newline()?;
                            let th = p.block(|p| p.rule_then())?;
                            let th = th.into_iter().next().ok_or((p.line(), "empty rule".to_string()))?;
                            Ok((when, th))
                        } else {
                            let th = p.rule_then()?;
                            Ok((when, th))
                        }
                    })?;
                    let (when, then) = inner.into_iter().next().ok_or((line, "empty rule".to_string()))?;
                    Ok((trigger, for_every, when, then, Span { line, start, end: p.prev_end() }))
                })?;
                for (trigger, for_every, when, then, span) in items {
                    out = Some(Decl::Rule { name: name.clone(), private, trigger, for_every, when, then, span });
                }
                out.ok_or((line, "empty rule".to_string()))
            }
            "timeline" => {
                self.advance();
                self.expect_sym(":")?;
                self.newline()?;
                let evs = self.block(|p| p.event_decl())?;
                Ok(Decl::Timeline(evs))
            }
            "expect" => {
                self.advance();
                let time = if self.eat_kw("at") {
                    ExpectTime::At(self.time_ref()?)
                } else if self.eat_kw("before") {
                    ExpectTime::Before(self.time_ref()?)
                } else if self.eat_kw("throughout") {
                    let a = self.time_ref()?;
                    self.expect_sym("..")?;
                    let b = self.time_ref()?;
                    ExpectTime::Throughout(a, b)
                } else {
                    return self.err("expected 'at', 'before' or 'throughout'");
                };
                self.expect_sym(":")?;
                self.newline()?;
                let formulas = self.block(|p| {
                    let e = p.expr()?;
                    p.newline()?;
                    Ok(e)
                })?;
                Ok(Decl::Expect(Expect { time, formulas, span: self.span_from(start, line) }))
            }
            "time" => {
                self.advance();
                self.expect_kw("travel")?;
                self.expect_sym(":")?;
                let m = self.ident()?;
                if !matches!(m.as_str(), "overwrite" | "branching" | "fixed") {
                    return Err((line, format!("unknown time travel mode '{}': use overwrite, branching or fixed", m)));
                }
                self.newline()?;
                Ok(Decl::TimeTravel(m, self.span_from(start, line)))
            }
            "allow" => {
                self.advance();
                self.expect_kw("bootstrap")?;
                self.newline()?;
                Ok(Decl::AllowBootstrap)
            }
            _ => self.err("expected a declaration (agent, type, fact, action, rule, timeline, expect, world, …)"),
        }
    }

    fn rule_then(&mut self) -> PResult<RuleThen> {
        if self.eat_kw("do") {
            let c = self.call()?;
            self.newline()?;
            Ok(RuleThen::Do(c))
        } else {
            let a = self.primary()?;
            self.expect_kw("concludes")?;
            let f = self.expr()?;
            self.newline()?;
            Ok(RuleThen::Concludes(a, f))
        }
    }

    fn action_clause(&mut self) -> PResult<ActionClause> {
        if self.eat_kw("needs") {
            self.expect_sym(":")?;
            let e = self.expr()?;
            self.newline()?;
            Ok(ActionClause::Needs(e))
        } else if self.eat_kw("effect") {
            self.expect_sym(":")?;
            let mut v = vec![self.assign()?];
            while self.eat_sym(",") {
                v.push(self.assign()?);
            }
            self.newline()?;
            Ok(ActionClause::Effect(v))
        } else if self.is_kw("seen") {
            let (s, _) = self.seen_by()?;
            Ok(ActionClause::SeenBy(s))
        } else {
            self.err("expected 'needs:', 'effect:' or 'seen by:'")
        }
    }

    fn assign(&mut self) -> PResult<Assign> {
        let start = self.start();
        let line = self.line();
        let target = self.postfix_primary()?;
        self.expect_sym("=")?;
        let value = self.expr()?;
        let mut for_range = None;
        if self.eat_kw("for") {
            let v = self.ident()?;
            self.expect_kw("in")?;
            let lo = self.additive()?;
            self.expect_sym("..")?;
            let hi = self.additive()?;
            for_range = Some((v, lo, hi));
        }
        Ok(Assign { target, value, for_range, span: self.span_from(start, line) })
    }

    fn seen_by(&mut self) -> PResult<(Vec<SeenItem>, Span)> {
        let start = self.start();
        let line = self.line();
        self.expect_kw("seen")?;
        self.expect_kw("by")?;
        self.expect_sym(":")?;
        let mut items = Vec::new();
        loop {
            let who = if self.eat_kw("everyone") {
                Who::Everyone
            } else if self.eat_kw("nobody") {
                Who::Nobody
            } else if self.eat_kw("every") {
                let a = self.ident()?;
                let (ty, var) = if let Tok::Ident(b) = self.peek().clone() {
                    if !RESERVED.contains(&b.as_str()) {
                        self.advance();
                        (Some(a), b)
                    } else {
                        (None, a)
                    }
                } else {
                    (None, a)
                };
                let cond = if self.eat_kw("where") { Some(self.or_expr()?) } else { None };
                Who::Every { ty, var, cond }
            } else {
                Who::Agent(self.postfix_primary()?)
            };
            let mut mods = Vec::new();
            loop {
                if self.eat_kw("as") {
                    let mut calls = vec![self.call()?];
                    while self.eat_kw("then") {
                        calls.push(self.call()?);
                    }
                    mods.push(Modifier::As(calls));
                } else if self.eat_kw("hiding") {
                    mods.push(Modifier::Hiding(self.postfix_primary()?));
                } else if self.eat_kw("secretly") {
                    mods.push(Modifier::Secretly);
                } else {
                    break;
                }
            }
            items.push(SeenItem { who, mods });
            if !self.eat_sym(",") {
                break;
            }
        }
        self.newline()?;
        Ok((items, self.span_from(start, line)))
    }

    fn call(&mut self) -> PResult<Call> {
        let start = self.start();
        let line = self.line();
        let name = self.ident()?;
        let mut args = Vec::new();
        self.expect_sym("(")?;
        if !self.is_sym(")") {
            loop {
                args.push(self.call_arg()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        Ok(Call { name, args, span: self.span_from(start, line) })
    }

    fn call_arg(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let e = self.expr()?;
        if self.is_kw("as") && self.is_kw_at(1, "seen") {
            self.advance();
            self.advance();
            self.expect_kw("by")?;
            let by = self.postfix_primary()?;
            return Ok(self.mk(ExprKind::SeenAs { event: e, by }, start, line));
        }
        Ok(e)
    }

    fn event_decl(&mut self) -> PResult<EventDecl> {
        let start = self.start();
        let line = self.line();
        // repeated: night(k) for k in 1 .. n
        if matches!(self.peek(), Tok::Ident(_)) && matches!(self.peek_at(1), Tok::Sym("(")) {
            let c = self.call()?;
            self.expect_kw("for")?;
            let v = self.ident()?;
            self.expect_kw("in")?;
            let lo = self.additive()?;
            self.expect_sym("..")?;
            let hi = self.additive()?;
            self.newline()?;
            let clauses = if matches!(self.peek(), Tok::Indent) { self.block(|p| p.event_clause())? } else { vec![] };
            return Ok(EventDecl {
                label: c.name.clone(),
                repeat: Some((v, lo, hi)),
                label_args: c.args.clone(),
                actions: vec![c],
                because: None,
                clauses,
                span: self.span_from(start, line),
            });
        }
        let label = self.label()?;
        self.expect_sym(":")?;
        let mut actions = Vec::new();
        let mut because = None;
        if !matches!(self.peek(), Tok::Newline) {
            actions.push(self.call()?);
            while self.eat_kw("then") {
                actions.push(self.call()?);
            }
            if self.eat_kw("because") {
                because = Some(self.expr()?);
            }
        }
        self.newline()?;
        let clauses = if matches!(self.peek(), Tok::Indent) { self.block(|p| p.event_clause())? } else { vec![] };
        Ok(EventDecl { label, repeat: None, label_args: vec![], actions, because, clauses, span: self.span_from(start, line) })
    }

    fn event_clause(&mut self) -> PResult<EventClause> {
        let start = self.start();
        let line = self.line();
        if self.is_kw("seen") && self.is_kw_at(1, "by") {
            let (s, sp) = self.seen_by()?;
            return Ok(EventClause::SeenBy(s, sp));
        }
        // conclusion: <agent> concludes φ because … [despite …]
        let save = self.pos;
        if let Ok(agent) = self.postfix_primary() {
            if self.eat_kw("concludes") {
                let formula = self.expr_no_because()?;
                let because = if self.eat_kw("because") { Some(self.expr_no_because()?) } else { None };
                let despite = if self.eat_kw("despite") { Some(self.expr_no_because()?) } else { None };
                self.newline()?;
                return Ok(EventClause::Concludes(Conclusion { agent, formula, because, despite, span: self.span_from(start, line) }));
            }
        }
        self.pos = save;
        let a = self.assign()?;
        self.newline()?;
        Ok(EventClause::Assign(a))
    }

    fn expr_no_because(&mut self) -> PResult<E> {
        self.expr()
    }

    fn type_ref(&mut self) -> PResult<TypeRef> {
        if matches!(self.peek(), Tok::Int(_)) {
            let lo = self.additive()?;
            self.expect_sym("..")?;
            let hi = self.additive()?;
            return Ok(TypeRef::Range(lo, hi));
        }
        Ok(TypeRef::Named(self.ident()?))
    }

    fn time_ref(&mut self) -> PResult<TimeRef> {
        if self.eat_kw("start") {
            return Ok(TimeRef::Start);
        }
        if self.eat_kw("end") {
            return Ok(TimeRef::End);
        }
        if self.eat_kw("before") {
            return Ok(TimeRef::Before(Box::new(self.time_ref()?)));
        }
        let first = self.label()?;
        if self.is_sym(".") && matches!(self.peek_at(1), Tok::Ident(_) | Tok::Int(_)) {
            self.advance();
            if self.eat_kw("start") {
                return Ok(TimeRef::Start); // world-qualified start: rarely needed
            }
            if self.eat_kw("end") {
                return Ok(TimeRef::Event { world: Some(first), label: "end".into(), args: vec![] });
            }
            let label = self.label()?;
            let args = self.time_args()?;
            return Ok(TimeRef::Event { world: Some(first), label, args });
        }
        let args = self.time_args()?;
        Ok(TimeRef::Event { world: None, label: first, args })
    }

    fn time_args(&mut self) -> PResult<Vec<E>> {
        let mut args = Vec::new();
        if self.eat_sym("(") {
            loop {
                args.push(self.additive()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym(")")?;
        }
        Ok(args)
    }

    // ---------------------------------------------------------------- expressions

    pub fn expr(&mut self) -> PResult<E> {
        self.iff()
    }

    fn iff(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let l = self.implies()?;
        if self.eat_sym("<=>") {
            let r = self.iff()?;
            return Ok(self.mk(ExprKind::Bin(BinOp::Iff, l, r), start, line));
        }
        Ok(l)
    }

    fn implies(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let l = self.or_expr()?;
        if self.eat_sym("=>") {
            let r = self.implies()?;
            return Ok(self.mk(ExprKind::Bin(BinOp::Implies, l, r), start, line));
        }
        Ok(l)
    }

    fn or_expr(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let mut l = self.and_expr()?;
        while self.eat_kw("or") {
            let r = self.and_expr()?;
            l = self.mk(ExprKind::Bin(BinOp::Or, l, r), start, line);
        }
        Ok(l)
    }

    fn and_expr(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let mut l = self.not_expr()?;
        while self.eat_kw("and") {
            let r = self.not_expr()?;
            l = self.mk(ExprKind::Bin(BinOp::And, l, r), start, line);
        }
        Ok(l)
    }

    fn not_expr(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        if self.eat_kw("not") {
            let e = self.not_expr()?;
            return Ok(self.mk(ExprKind::Not(e), start, line));
        }
        self.comparison()
    }

    fn comparison(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let l = self.additive()?;
        // epistemic forms: A knows φ, A believes φ, A knows whether φ, A saw x
        if self.is_kw("knows") || self.is_kw("believes") {
            let mut mode = if self.is_kw("knows") { KMode::Knows } else { KMode::Believes };
            self.advance();
            if mode == KMode::Knows && self.eat_kw("whether") {
                mode = KMode::KnowsWhether;
            }
            let body = self.not_expr()?;
            return Ok(self.mk(ExprKind::Epistemic { agent: l, mode, body }, start, line));
        }
        if self.eat_kw("saw") {
            let what = self.additive()?;
            return Ok(self.mk(ExprKind::Saw { agent: l, what }, start, line));
        }
        let op = match self.peek() {
            Tok::Sym("=") => BinOp::Eq,
            Tok::Sym("!=") => BinOp::Ne,
            Tok::Sym("<") => BinOp::Lt,
            Tok::Sym("<=") => BinOp::Le,
            Tok::Sym(">") => BinOp::Gt,
            Tok::Sym(">=") => BinOp::Ge,
            _ => return Ok(l),
        };
        self.advance();
        let r = self.additive()?;
        Ok(self.mk(ExprKind::Bin(op, l, r), start, line))
    }

    fn additive(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let mut l = self.term()?;
        loop {
            let op = if self.is_sym("+") {
                BinOp::Add
            } else if self.is_sym("-") {
                BinOp::Sub
            } else {
                break;
            };
            self.advance();
            let r = self.term()?;
            l = self.mk(ExprKind::Bin(op, l, r), start, line);
        }
        Ok(l)
    }

    fn term(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let mut l = self.unary()?;
        while self.eat_sym("*") {
            let r = self.unary()?;
            l = self.mk(ExprKind::Bin(BinOp::Mul, l, r), start, line);
        }
        Ok(l)
    }

    fn unary(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        if self.eat_sym("-") {
            let e = self.unary()?;
            return Ok(self.mk(ExprKind::Neg(e), start, line));
        }
        self.postfix_primary()
    }

    fn postfix_primary(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        let mut e = self.primary()?;
        loop {
            if self.is_sym(".") && matches!(self.peek_at(1), Tok::Ident(_)) {
                self.advance();
                let f = self.ident()?;
                e = self.mk(ExprKind::Field(e, f), start, line);
            } else if self.is_kw("at") && !matches!(self.peek_at(1), Tok::Sym(":")) {
                self.advance();
                let t = self.time_ref()?;
                e = self.mk(ExprKind::At(e, t), start, line);
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn primary(&mut self) -> PResult<E> {
        let start = self.start();
        let line = self.line();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.advance();
                Ok(self.mk(ExprKind::Int(n), start, line))
            }
            Tok::Sym("(") => {
                self.advance();
                let first = self.expr()?;
                if self.eat_sym(",") {
                    let mut items = vec![first];
                    loop {
                        items.push(self.expr()?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                    self.expect_sym(")")?;
                    return Ok(self.mk(ExprKind::Tuple(items), start, line));
                }
                self.expect_sym(")")?;
                // keep the parenthesised span for messages
                Ok(first)
            }
            Tok::Ident(s) => {
                match s.as_str() {
                    "true" | "false" => {
                        self.advance();
                        return Ok(self.mk(ExprKind::Bool(s == "true"), start, line));
                    }
                    "all" | "some" => {
                        self.advance();
                        let var = self.ident()?;
                        self.expect_kw("in")?;
                        let ty = self.type_ref()?;
                        self.expect_sym(":")?;
                        let body = self.expr()?;
                        return Ok(self.mk(ExprKind::Quant { all: s == "all", var, ty, body }, start, line));
                    }
                    "common" => {
                        self.advance();
                        self.expect_kw("knowledge")?;
                        let group = if self.eat_kw("among") { Some(self.ident()?) } else { None };
                        self.expect_sym(":")?;
                        let body = self.expr()?;
                        return Ok(self.mk(ExprKind::Common { group, body }, start, line));
                    }
                    "deducible" => {
                        self.advance();
                        self.expect_kw("by")?;
                        let agent = self.postfix_primary()?;
                        self.expect_sym(":")?;
                        let body = self.expr()?;
                        return Ok(self.mk(ExprKind::Deducible { agent, body }, start, line));
                    }
                    "possible" => {
                        self.advance();
                        self.expect_kw("for")?;
                        let agent = self.postfix_primary()?;
                        self.expect_sym(":")?;
                        let body = self.expr()?;
                        return Ok(self.mk(ExprKind::Possible { agent, body }, start, line));
                    }
                    _ => {}
                }
                if RESERVED.contains(&s.as_str()) {
                    return self.err("expected an expression");
                }
                self.advance();
                if self.is_sym(".") && matches!(self.peek_at(1), Tok::Ident(_)) {
                    // World.name — only if the first is capitalised and the next is a plain name
                    if s.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) && self.is_world_qualifier(&s) {
                        self.advance();
                        let n = self.ident()?;
                        return Ok(self.mk(ExprKind::Qualified(s, n), start, line));
                    }
                }
                if self.eat_sym("(") {
                    let mut args = Vec::new();
                    if !self.is_sym(")") {
                        loop {
                            args.push(self.call_arg()?);
                            if !self.eat_sym(",") {
                                break;
                            }
                        }
                    }
                    self.expect_sym(")")?;
                    return Ok(self.mk(ExprKind::Call(s, args), start, line));
                }
                if self.eat_sym("[") {
                    let i = self.expr()?;
                    self.expect_sym("]")?;
                    return Ok(self.mk(ExprKind::Index(s, i), start, line));
                }
                Ok(self.mk(ExprKind::Name(s), start, line))
            }
            _ => self.err("expected an expression"),
        }
    }

    /// Set by the driver: names of worlds, so `Tale.e1` parses as a qualified name.
    fn is_world_qualifier(&self, s: &str) -> bool {
        WORLD_NAMES.with(|w| w.borrow().iter().any(|x| x == s))
    }
}

thread_local! {
    pub static WORLD_NAMES: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

enum ActionClause {
    Needs(E),
    Effect(Vec<Assign>),
    SeenBy(Vec<SeenItem>),
}

/// Pre-scan for `world X` declarations so qualified names parse.
pub fn scan_world_names(toks: &[Token]) -> Vec<String> {
    let mut out = Vec::new();
    for w in toks.windows(2) {
        if let (Tok::Ident(a), Tok::Ident(b)) = (&w[0].tok, &w[1].tok) {
            if a == "world" {
                out.push(b.clone());
            }
        }
    }
    out
}
