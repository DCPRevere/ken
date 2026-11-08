//! Runtime values.

use crate::ast::E;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub type Env = Vec<(Rc<str>, Value)>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Sym(Rc<str>),
    Agent(u16, u32), // (world, agent index)
    Tuple(Rc<[Value]>),
    Unknown,
    Formula(Rc<FormulaVal>),
    Event(Rc<EventRef>),
}

#[derive(Debug)]
pub struct FormulaVal {
    pub expr: E,
    pub env: Env,
    pub world: usize,
}
impl PartialEq for FormulaVal {
    fn eq(&self, o: &Self) -> bool {
        Rc::ptr_eq(&self.expr, &o.expr) && self.env == o.env
    }
}
impl Eq for FormulaVal {}
impl Hash for FormulaVal {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (Rc::as_ptr(&self.expr) as usize).hash(h);
        self.env.hash(h);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EventRef {
    pub world: usize,
    pub label: String,
    pub seen_by: Option<(u16, u32)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ActionInst {
    pub name: Rc<str>,
    pub args: Vec<Value>,
}

impl Value {
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }
    pub fn as_agent(&self) -> Option<(u16, u32)> {
        match self {
            Value::Agent(w, a) => Some((*w, *a)),
            _ => None,
        }
    }
}

pub fn env_get<'a>(env: &'a Env, name: &str) -> Option<&'a Value> {
    env.iter().rev().find(|(n, _)| &**n == name).map(|(_, v)| v)
}

pub fn env_with(env: &Env, name: &str, v: Value) -> Env {
    let mut e = env.clone();
    e.push((Rc::from(name), v));
    e
}
