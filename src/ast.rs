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
    Quant { all: bool, var: String, ty: TypeRef, body: E },
    Epistemic { agent: E, mode: KMode, body: E },
    Common { group: Option<String>, body: E },
    Deducible { agent: E, body: E },
    Possible { agent: E, body: E },
    Saw { agent: E, what: E },
    At(E, TimeRef),
    SeenAs { event: E, by: E },
}

#[derive(Clone, Debug)]
pub enum TimeRef {
    Start,
    End,
    Event { world: Option<String>, label: String, args: Vec<E> },
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
    Every { ty: Option<String>, var: String, cond: Option<E> },
}

#[derive(Clone, Debug)]
pub enum Modifier {
    As(Vec<Call>),
    Hiding(E),
    Secretly,
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
}

#[derive(Clone, Debug)]
pub struct EventDecl {
    pub label: String,
    pub repeat: Option<(String, E, E)>, // night(k) for k in 1 .. n
    pub label_args: Vec<E>,             // the call args for repeated events, e.g. [k]
    pub actions: Vec<Call>,
    pub because: Option<E>,
    pub clauses: Vec<EventClause>,
    pub span: Span,
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
    Agent { names: Vec<AgentName>, mode: Option<Mode>, sees_all_of: Option<String>, span: Span },
    Segment { name: String, origin_world: Option<String>, origin: String, at: TimeRef, span: Span },
    Type { name: String, def: TypeDef, span: Span },
    Fact { name: String, params: Vec<TypeRef>, ty: TypeRef, default: Option<E>, domain: Option<Vec<E>>, span: Span },
    Action { name: String, params: Vec<(String, Option<TypeRef>)>, needs: Vec<E>, effects: Vec<Assign>, seen_by: Option<Vec<SeenItem>>, span: Span },
    Rule { name: String, private: bool, trigger: Trigger, for_every: Option<(String, String)>, when: Option<E>, then: RuleThen, span: Span },
    Timeline(Vec<EventDecl>),
    Expect(Expect),
    TimeTravel(String, Span),
    AllowBootstrap,
    World { name: String, about: Vec<String>, revises: Option<(String, TimeRef)>, decls: Vec<Decl>, span: Span },
}
