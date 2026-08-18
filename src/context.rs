use crate::{bail, Result, Value};
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

    /// Build a context from any serializable map or struct.
    #[cfg(feature = "serde")]
    pub fn from_serialize<T: serde::Serialize + ?Sized>(value: &T) -> Result<Self> {
        crate::to_value(value)?.try_into()
    }
}

/// A borrowed source of values used while evaluating an expression.
///
/// Implementing this trait allows callers and custom functions to provide
/// context values without cloning an entire [`Context`] for each evaluation.
pub trait ContextProvider {
    fn get(&self, key: &str) -> Option<&Value>;

    /// Materialize the values visible to the expression.
    ///
    /// Evaluation only calls this when an expression accesses `$env`.
    fn to_context(&self) -> Context;

    #[doc(hidden)]
    fn environment(&self) -> Context {
        self.to_context()
    }
}

impl ContextProvider for Context {
    fn get(&self, key: &str) -> Option<&Value> {
        self.get(key)
    }

    fn to_context(&self) -> Context {
        self.clone()
    }
}

pub(crate) struct ContextScope<'a> {
    parent: &'a dyn ContextProvider,
    values: Context,
}

impl<'a> ContextScope<'a> {
    pub(crate) fn new(parent: &'a dyn ContextProvider) -> Self {
        Self {
            parent,
            values: Context::default(),
        }
    }

    pub(crate) fn insert<K, V>(&mut self, key: K, value: V)
    where
        K: Into<String>,
        V: Into<Value>,
    {
        self.values.insert(key, value);
    }
}

impl ContextProvider for ContextScope<'_> {
    fn get(&self, key: &str) -> Option<&Value> {
        self.values.get(key).or_else(|| self.parent.get(key))
    }

    fn to_context(&self) -> Context {
        let mut context = self.parent.to_context();
        for (key, value) in &self.values.0 {
            context.insert(key.clone(), value.clone());
        }
        context
    }

    fn environment(&self) -> Context {
        self.parent.environment()
    }
}

impl TryFrom<Value> for Context {
    type Error = crate::Error;

    fn try_from(value: Value) -> Result<Self> {
        match value {
            Value::Map(values) => Ok(Self(values)),
            value => bail!("context must be a map, got {value:?}"),
        }
    }
}

impl<S: Display, T: Into<Value>> FromIterator<(S, T)> for Context {
    fn from_iter<I: IntoIterator<Item = (S, T)>>(iter: I) -> Self {
        let mut ctx = Self::default();
        for (k, v) in iter {
            ctx.insert(k.to_string(), v);
        }
        ctx
    }
}

#[cfg(all(test, feature = "serde"))]
mod tests {
    use super::Context;
    use serde::Serialize;

    #[derive(Serialize)]
    struct Settings<'a> {
        name: &'a str,
        retries: u8,
    }

    #[test]
    fn context_from_serializable_struct() {
        let context = Context::from_serialize(&Settings {
            name: "mise",
            retries: 3,
        })
        .unwrap();

        assert_eq!(context.get("name").unwrap().as_string(), Some("mise"));
        assert_eq!(context.get("retries").unwrap().as_integer(), Some(3));
    }

    #[test]
    fn context_rejects_non_map_values() {
        assert!(Context::from_serialize(&[1, 2, 3]).is_err());
    }
}
