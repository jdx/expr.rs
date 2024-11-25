use indexmap::IndexMap;
use std::fmt::Display;
use crate::ExprValue;

#[derive(Debug, Clone, Default)]
pub struct ExprContext(pub(crate) IndexMap<String, ExprValue>);

impl ExprContext {
    pub fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<String>,
        V: Into<ExprValue>,
    {
        self.0.insert(key.into(), value.into());
    }

    pub fn get(&self, key: &str) -> Option<&ExprValue> {
        self.0.get(key)
    }
}

impl<S: Display, T: Into<ExprValue>> FromIterator<(S, T)> for ExprContext {
    fn from_iter<I: IntoIterator<Item = (S, T)>>(iter: I) -> Self {
        let mut ctx = Self::default();
        for (k, v) in iter {
            ctx.insert(k.to_string(), v);
        }
        ctx
    }
}
