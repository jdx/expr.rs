use indexmap::IndexMap;
use std::fmt::{Display, Formatter};
use std::fmt;

/// Represents a data value as input or output to an expr program
#[derive(Debug, PartialEq, Clone)]
pub enum ExprValue {
    Number(i64),
    Bool(bool),
    Float(f64),
    Nil,
    String(String),
    Array(Vec<ExprValue>),
    Map(IndexMap<String, ExprValue>),
}

impl ExprValue {
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            ExprValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_number(&self) -> Option<i64> {
        match self {
            ExprValue::Number(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<f64> {
        match self {
            ExprValue::Float(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match self {
            ExprValue::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[ExprValue]> {
        match self {
            ExprValue::Array(a) => Some(a),
            _ => None,
        }
    }

    pub fn as_map(&self) -> Option<&IndexMap<String, ExprValue>> {
        match self {
            ExprValue::Map(m) => Some(m),
            _ => None,
        }
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, ExprValue::Nil)
    }
}

impl AsRef<ExprValue> for ExprValue {
    fn as_ref(&self) -> &ExprValue {
        self
    }
}

impl From<i64> for ExprValue {
    fn from(n: i64) -> Self {
        ExprValue::Number(n)
    }
}

impl From<f64> for ExprValue {
    fn from(f: f64) -> Self {
        ExprValue::Float(f)
    }
}

impl From<bool> for ExprValue {
    fn from(b: bool) -> Self {
        ExprValue::Bool(b)
    }
}

impl From<String> for ExprValue {
    fn from(s: String) -> Self {
        ExprValue::String(s)
    }
}

impl From<&String> for ExprValue {
    fn from(s: &String) -> Self {
        ExprValue::String(s.to_string())
    }
}

impl From<&str> for ExprValue {
    fn from(s: &str) -> Self {
        ExprValue::String(s.to_string())
    }
}

impl<V: Into<ExprValue>> From<Vec<V>> for ExprValue {
    fn from(a: Vec<V>) -> Self {
        ExprValue::Array(a.into_iter().map(|v| v.into()).collect())
    }
}

impl From<IndexMap<String, ExprValue>> for ExprValue {
    fn from(m: IndexMap<String, ExprValue>) -> Self {
        ExprValue::Map(m)
    }
}

impl Display for ExprValue {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ExprValue::Number(n) => write!(f, "{n}"),
            ExprValue::Float(n) => write!(f, "{n}"),
            ExprValue::Bool(b) => write!(f, "{b}"),
            ExprValue::Nil => write!(f, "nil"),
            ExprValue::String(s) => write!(
                f,
                r#""{}""#,
                s.replace("\\", "\\\\")
                    .replace("\n", "\\n")
                    .replace("\r", "\\r")
                    .replace("\t", "\\t")
                    .replace("\"", "\\\"")
            ),
            ExprValue::Array(a) => write!(
                f,
                "[{}]",
                a.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            ExprValue::Map(m) => write!(
                f,
                "{{{}}}",
                m.iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}
