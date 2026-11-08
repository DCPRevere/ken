//! State recorded while running a world.

use crate::kripke::Model;
use crate::value::{ActionInst, Value};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
    Note,
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub level: Level,
    pub line: usize,
    pub world: String,
    pub at: Option<String>,
    pub msg: String,
}

/// What one agent believes happened at one event.
#[derive(Clone, Debug, PartialEq)]
pub struct ViewRec {
    pub actions: Vec<ActionInst>,
    pub direct: bool,
    pub step: usize,
    pub actual: Vec<ActionInst>,
}

#[derive(Clone, Debug, Default)]
pub struct Registry {
    pub views: Vec<HashMap<String, ViewRec>>,
}

impl Registry {
    pub fn new(n_agents: usize) -> Self {
        Registry { views: vec![HashMap::new(); n_agents] }
    }
}

/// Identifies a conclusion: (step, index within step or rule-derived key).
pub type CKey = (usize, String);

#[derive(Clone, Debug)]
pub struct ConclRec {
    pub key: CKey,
    pub agent: u32,
    pub formula: Value, // Value::Formula
    pub event_sources: Vec<(usize, String)>, // (world, label)
    pub belief_sources: Vec<Value>,
    pub despite: Vec<(usize, String)>,
    pub step: usize,
    pub snapshot: Vec<Option<Vec<ActionInst>>>, // views of event sources when concluded
    pub foreign: Option<usize>,                // target world, if about another world
    pub line: usize,
}

/// A person's beliefs about another world (e.g. a reader about the tale).
#[derive(Clone, Debug, Default)]
pub struct ForeignStore {
    pub views: HashMap<String, (Vec<ActionInst>, usize)>,
    pub active: Vec<ConclRec>,
}

pub type ForeignMap = HashMap<(u32, usize), ForeignStore>;

#[derive(Clone)]
pub struct Snap {
    pub model: Rc<Model>,
    pub registry: Rc<Registry>,
    pub foreign: Rc<ForeignMap>,
    pub actual: Vec<ActionInst>,
    pub disabled: Rc<HashSet<CKey>>,
}

pub struct Run {
    #[allow(dead_code)]
    pub world: usize,
    pub snaps: Vec<Snap>,
    pub diags: Vec<Diag>,
    pub conclusions: Vec<ConclRec>,
    pub seg_beliefs: HashMap<u32, Vec<(usize, Value)>>,
}
