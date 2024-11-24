use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub enum Value {
    Number(i32),
    String(String),
    Bool(bool),
}

impl From<i32> for Value {
    fn from(n: i32) -> Self {
        Value::Number(n)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_string())
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{n}"),
            Value::String(s) => write!(f, r#""{s}""#),
            Value::Bool(b) => write!(f, "{b}"),
        }
    }
}
