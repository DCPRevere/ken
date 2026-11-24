//! Syntax tree.

use std::rc::Rc;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub line: usize,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    And,
    Or,
    Implies,
    Iff,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KMode {
    Knows,
    Believes,
    KnowsWhether,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub type E = Rc<Expr>;

#[derive(Debug)]
pub enum ExprKind {
    Int(i64),
    Bool(bool),
    Name(String),
    Qualified(String, String), // World.name
    Call(String, Vec<E>),
    Index(String, E),
    Field(E, String),
    Tuple(Vec<E>),
    Not(E),
    Neg(E),
    Bin(BinOp, E, E),
    Quant {
        all: bool,
        var: String,
        ty: TypeRef,
        body: E,
    },
    Epistemic {
        agent: E,
        mode: KMode,
        body: E,
    },
    Common {
        group: Option<String>,
        body: E,
    },
    Deducible {
        agent: E,
        body: E,
    },
    Possible {
        agent: E,
        body: E,
    },
    Saw {
        agent: E,
        what: E,
    },
    At(E, TimeRef),
    SeenAs {
        event: E,
        by: E,
    },
    /// `A wants φ`
    Wants {
        agent: E,
        body: E,
    },
    /// `A suspects φ`
    Suspects {
        agent: E,
        body: E,
    },
}

#[derive(Clone, Debug)]
pub enum TimeRef {
    Start,
    End,
    Event {
        world: Option<String>,
        label: String,
        args: Vec<E>,
    },
    Before(Box<TimeRef>),
}

#[derive(Clone, Debug)]
pub enum TypeRef {
    Named(String),
    Range(E, E),
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    Enum(Vec<String>),
    Range(E, E),
    Record(Vec<(String, TypeRef)>),
}

#[derive(Clone, Debug)]
pub struct Call {
    pub name: String,
    pub args: Vec<E>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Assign {
    pub target: E,
    pub value: E,
    pub for_range: Option<(String, E, E)>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Who {
    Everyone,
    Nobody,
    Agent(E),
    Every {
        ty: Option<String>,
        var: String,
        cond: Option<E>,
    },
}

#[derive(Clone, Debug)]
pub enum Modifier {
    As(Vec<Call>),
    Hiding(E),
    /// `secretly`, or `secretly except X and Y`: those listed know about the observer
    Secretly(Vec<E>),
}

#[derive(Clone, Debug)]
pub struct SeenItem {
    pub who: Who,
    pub mods: Vec<Modifier>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Person,
    Logician,
}

#[derive(Clone, Debug)]
pub struct AgentName {
    pub base: String,
    pub range: Option<(E, E)>,
}

#[derive(Clone, Debug)]
pub enum Trigger {
    After(Call),
    AfterSees(E, Call),
}

#[derive(Clone, Debug)]
pub enum RuleThen {
    Do(Call),
    Concludes(E, E),
}

#[derive(Clone, Debug)]
pub struct Conclusion {
    pub agent: E,
    pub formula: E,
    pub because: Option<E>,
    pub despite: Option<E>,
    pub span: Span,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub enum EventClause {
    SeenBy(Vec<SeenItem>, Span),
    Concludes(Conclusion),
    Assign(Assign),
    /// `A wants φ` / `A no longer wants φ`
    Wants {
        agent: E,
        formula: E,
        on: bool,
        span: Span,
    },
    /// `A suspects φ because …`: a belief held loosely
    Suspects(Conclusion),
    /// `A watches <fact>` / `A no longer watches <fact>`: A sees its value at every step
    Watches {
        agent: E,
        what: E,
        on: bool,
        span: Span,
    },
    /// `A forgets <fact>` or `A forgets <event>`
    Forgets {
        agent: E,
        what: E,
        span: Span,
    },
}

#[derive(Clone, Debug)]
pub struct EventDecl {
    pub label: String,
    pub repeat: Option<(String, E, E)>, // night(k) for k in 1 .. n
    pub label_args: Vec<E>,             // the call args for repeated events, e.g. [k]
    pub actions: Vec<Call>,
    pub because: Option<E>,
    /// `so that φ`: what the actor means to bring about
    pub purpose: Option<E>,
    /// `e1 @ 10:` the clock time of the event
    pub time: Option<E>,
    pub clauses: Vec<EventClause>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum UseTarget {
    /// a library that ships with Ken
    Builtin(String),
    /// a file, relative to the file that uses it
    Path(String),
}

#[derive(Clone, Debug)]
pub enum ExpectTime {
    At(TimeRef),
    Before(TimeRef),
    Throughout(TimeRef, TimeRef),
}

#[derive(Clone, Debug)]
pub struct Expect {
    pub time: ExpectTime,
    pub formulas: Vec<E>,
    pub span: Span,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub enum Decl {
    Given(Vec<(String, Option<E>)>),
    Agent {
        names: Vec<AgentName>,
        mode: Option<Mode>,
        sees_all_of: Option<String>,
        span: Span,
    },
    Segment {
        name: String,
        origin_world: Option<String>,
        origin: String,
        at: TimeRef,
        span: Span,
    },
    Type {
        name: String,
        def: TypeDef,
        span: Span,
    },
    Fact {
        name: String,
        params: Vec<TypeRef>,
        ty: TypeRef,
        default: Option<E>,
        domain: Option<Vec<E>>,
        span: Span,
    },
    Action {
        name: String,
        params: Vec<(String, Option<TypeRef>)>,
        needs: Vec<E>,
        effects: Vec<Assign>,
        seen_by: Option<Vec<SeenItem>>,
        unseen: bool,
        span: Span,
    },
    /// `use space`, `use "lib/court.ken" as court`
    Use {
        target: UseTarget,
        alias: Option<String>,
        span: Span,
    },
    /// left where a library was spliced in: (library, alias)
    Used {
        lib: String,
        alias: String,
    },
    Rule {
        name: String,
        private: bool,
        trigger: Trigger,
        for_every: Option<(String, String)>,
        when: Option<E>,
        then: RuleThen,
        span: Span,
    },
    Timeline(Vec<EventDecl>),
    Expect(Expect),
    TimeTravel(String, Span),
    AllowBootstrap,
    World {
        name: String,
        about: Vec<String>,
        revises: Option<(String, TimeRef)>,
        decls: Vec<Decl>,
        span: Span,
    },
}

/// Do two expressions say the same thing (ignoring layout)?
pub fn same_expr(a: &E, b: &E) -> bool {
    use ExprKind::*;
    let tr =
        |x: &TimeRef, y: &TimeRef| format!("{:?}", strip_time(x)) == format!("{:?}", strip_time(y));
    match (&a.kind, &b.kind) {
        (Int(x), Int(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Name(x), Name(y)) => x == y,
        (Qualified(w1, n1), Qualified(w2, n2)) => w1 == w2 && n1 == n2,
        (Call(n1, a1), Call(n2, a2)) => {
            n1 == n2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| same_expr(x, y))
        }
        (Index(n1, i1), Index(n2, i2)) => n1 == n2 && same_expr(i1, i2),
        (Field(b1, f1), Field(b2, f2)) => f1 == f2 && same_expr(b1, b2),
        (Tuple(x), Tuple(y)) => x.len() == y.len() && x.iter().zip(y).all(|(p, q)| same_expr(p, q)),
        (Not(x), Not(y)) | (Neg(x), Neg(y)) => same_expr(x, y),
        (Bin(o1, a1, b1), Bin(o2, a2, b2)) => o1 == o2 && same_expr(a1, a2) && same_expr(b1, b2),
        (
            Quant {
                all: q1,
                var: v1,
                body: b1,
                ..
            },
            Quant {
                all: q2,
                var: v2,
                body: b2,
                ..
            },
        ) => q1 == q2 && v1 == v2 && same_expr(b1, b2),
        (
            Epistemic {
                agent: a1,
                mode: m1,
                body: b1,
            },
            Epistemic {
                agent: a2,
                mode: m2,
                body: b2,
            },
        ) => m1 == m2 && same_expr(a1, a2) && same_expr(b1, b2),
        (
            Common {
                group: g1,
                body: b1,
            },
            Common {
                group: g2,
                body: b2,
            },
        ) => g1 == g2 && same_expr(b1, b2),
        (
            Deducible {
                agent: a1,
                body: b1,
            },
            Deducible {
                agent: a2,
                body: b2,
            },
        )
        | (
            Possible {
                agent: a1,
                body: b1,
            },
            Possible {
                agent: a2,
                body: b2,
            },
        )
        | (
            Wants {
                agent: a1,
                body: b1,
            },
            Wants {
                agent: a2,
                body: b2,
            },
        )
        | (
            Suspects {
                agent: a1,
                body: b1,
            },
            Suspects {
                agent: a2,
                body: b2,
            },
        ) => same_expr(a1, a2) && same_expr(b1, b2),
        (
            Saw {
                agent: a1,
                what: w1,
            },
            Saw {
                agent: a2,
                what: w2,
            },
        ) => same_expr(a1, a2) && same_expr(w1, w2),
        (At(x, t1), At(y, t2)) => same_expr(x, y) && tr(t1, t2),
        (SeenAs { event: e1, by: b1 }, SeenAs { event: e2, by: b2 }) => {
            same_expr(e1, e2) && same_expr(b1, b2)
        }
        _ => false,
    }
}

fn strip_time(t: &TimeRef) -> String {
    match t {
        TimeRef::Start => "start".into(),
        TimeRef::End => "end".into(),
        TimeRef::Before(x) => format!("before {}", strip_time(x)),
        TimeRef::Event { world, label, args } => format!("{:?}.{}({})", world, label, args.len()),
    }
}
