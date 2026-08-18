use crate::Value;
use indexmap::IndexMap;
use std::fmt::Display;

#[derive(Debug, Clone, Default)]
pub struct Context(pub(crate) IndexMap<String, Value>);

impl Context {
    pub fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<String>,
        V: Into<Value>,
    {
        self.0.insert(key.into(), value.into());
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.0.get(key)
    }
}

pub(crate) trait ContextLookup {
    fn lookup(&self, key: &str) -> Option<&Value>;
    fn extend_map(&self, map: &mut IndexMap<String, Value>);
}

impl ContextLookup for Context {
    fn lookup(&self, key: &str) -> Option<&Value> {
        self.get(key)
    }

    fn extend_map(&self, map: &mut IndexMap<String, Value>) {
        map.extend(self.0.iter().map(|(key, value)| (key.clone(), value.clone())));
    }
}

/// A read-only view of the variables visible during evaluation.
///
/// Function callbacks receive this type as their `ctx` field. Use
/// [`EvalContext::get`] for lookups, or [`EvalContext::to_context`] when an owned
/// context is required.
pub struct EvalContext<'a> {
    parent: &'a dyn ContextLookup,
    binding: Option<(&'a str, &'a Value)>,
    locals: IndexMap<String, Value>,
}

impl<'a> EvalContext<'a> {
    pub(crate) fn new(parent: &'a dyn ContextLookup) -> Self {
        Self {
            parent,
            binding: None,
            locals: IndexMap::new(),
        }
    }

    pub(crate) fn with_binding(
        parent: &'a dyn ContextLookup,
        key: &'a str,
        value: &'a Value,
    ) -> Self {
        Self {
            parent,
            binding: Some((key, value)),
            locals: IndexMap::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&Value> {
        self.lookup(key)
    }

    pub fn to_context(&self) -> Context {
        let mut map = IndexMap::new();
        self.extend_map(&mut map);
        Context(map)
    }

    pub(crate) fn environment_context(&self) -> Context {
        let mut map = IndexMap::new();
        self.parent.extend_map(&mut map);
        if let Some((key, value)) = self.binding {
            map.insert(key.to_string(), value.clone());
        }
        Context(map)
    }

    pub(crate) fn insert(&mut self, key: String, value: Value) {
        self.locals.insert(key, value);
    }
}

impl ContextLookup for EvalContext<'_> {
    fn lookup(&self, key: &str) -> Option<&Value> {
        self.locals.get(key).or_else(|| {
            self.binding
                .filter(|(binding, _)| *binding == key)
                .map(|(_, value)| value)
                .or_else(|| self.parent.lookup(key))
        })
    }

    fn extend_map(&self, map: &mut IndexMap<String, Value>) {
        self.parent.extend_map(map);
        if let Some((key, value)) = self.binding {
            map.insert(key.to_string(), value.clone());
        }
        map.extend(
            self.locals
                .iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
    }
}

impl<S: Display, T: Into<Value>> FromIterator<(S, T)> for Context {
    fn from_iter<I: IntoIterator<Item=(S, T)>>(iter: I) -> Self {
        let mut ctx = Self::default();
        for (k, v) in iter {
            ctx.insert(k.to_string(), v);
        }
        ctx
    }
}
