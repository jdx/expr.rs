//! Implementation of [expr](https://expr-lang.org) in rust
//!
//! Example:
//! ```
//! use std::collections::HashMap;
//! use expr::ExprParser;
//! let p = ExprParser::new();
//! let ctx: HashMap<String, String> = HashMap::new();
//! assert_eq!(p.eval("1 + 2", ctx).unwrap().to_string(), "3");
//! ```

use indexmap::IndexMap;
use lalrpop_util::lalrpop_mod;
use std::collections::HashMap;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::iter::once;
use thiserror::Error;

/// An error that can occur when parsing or evaluating an expr program
#[derive(Error, Debug)]
pub enum ExprError {
    #[error("Parse error: {0}")]
    ParseError(String),
    #[error("Eval error: {0}")]
    EvalError(String),
    #[error("Regex error: {0}")]
    RegexError(#[from] regex::Error),
}


impl From<String> for ExprError {
    fn from(s: String) -> Self {
        ExprError::EvalError(s)
    }
}

type Result<T> = std::result::Result<T, ExprError>;

macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::ExprError::EvalError(format!($($arg)*)))
    };
}

/// A parsed expr program that can be run
#[derive(Debug, Clone)]
pub struct ExprProgram {
    expr: Expr,
}

/// Represents a data value as input or output to an expr program
#[derive(Debug, PartialEq, Clone)]
pub enum ExprValue {
    Number(i32),
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

    pub fn as_number(&self) -> Option<i32> {
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

impl From<i32> for ExprValue {
    fn from(n: i32) -> Self {
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

impl From<Vec<ExprValue>> for ExprValue {
    fn from(a: Vec<ExprValue>) -> Self {
        ExprValue::Array(a)
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
            ExprValue::String(s) => write!(f, r#""{}""#, s
                .replace("\\", "\\\\")
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

#[derive(Debug, Clone)]
enum Expr {
    Number(i32),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,
    ID(String),
    Array(Vec<Box<Expr>>),
    Map(IndexMap<String, Box<Expr>>),
    Not(Box<Expr>),
    Op(Box<Expr>, Opcode, Box<Expr>),
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    NilCoalesce(Box<Expr>, Box<Expr>),
    Func(String, Vec<Box<Expr>>),
    Pipe(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn unescape_str(s: &str) -> Self {
        Expr::String(s
            .replace("\\\\", "\\")
            .replace("\\n", "\n")
            .replace("\\r", "\r")
            .replace("\\t", "\t")
            .replace("\\\"", "\""))
    }
}


#[derive(Debug, Clone)]
enum Opcode {
    Add,
    Sub,
    Mul,
    Mod,
    Div,
    Pow,
    And,
    Or,
    Eq,
    Lt,
    Gt,
    Lte,
    Gte,
    Ne,
    In,
    Contains,
    StartsWith,
    EndsWith,
    Matches,
    Index,
    OptIndex,
}

/// Main struct for parsing and evaluating expr programs
///
/// Example:
///
/// ```
/// use std::collections::HashMap;
/// use expr::ExprParser;
/// let ctx = HashMap::from([("foo", 1), ("bar", 2)]);
/// let p = ExprParser::new();
/// assert_eq!(p.eval("foo + bar", ctx).unwrap().to_string(), "3");
/// ```
#[derive(Default)]
pub struct ExprParser<'a> {
    functions: HashMap<String, Box<dyn Fn(&Vec<ExprValue>) -> Result<ExprValue> + 'a + Sync + Send>>,
}

impl Debug for ExprParser<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("ExprParser").finish()
    }
}

lalrpop_mod!(grammar);

impl<'a> ExprParser<'a> {
    /// Create a new parser
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }

    /// Add a function for expr programs to call
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{ExprParser, ExprValue};
    ///
    /// let mut p = ExprParser::new();
    /// p.add_function("add", |args| {
    ///   let mut sum = 0;
    ///     for arg in args {
    ///       if let ExprValue::Number(n) = arg {
    ///         sum += n;
    ///        } else {
    ///          panic!("Invalid argument: {arg:?}");
    ///        }
    ///     }
    ///   Ok(sum.into())
    /// });
    /// let ctx: HashMap<String, String> = HashMap::new();
    /// assert_eq!(p.eval("add(1, 2, 3)", ctx).unwrap().to_string(), "6");
    /// ```
    pub fn add_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&Vec<ExprValue>) -> Result<ExprValue> + 'a + Sync + Send,
    {
        self.functions.insert(name.to_string(), Box::new(f));
    }

    /// Parse an expr program to be run later
    pub fn compile(&self, code: &str) -> Result<ExprProgram> {
        Ok(ExprProgram {
            expr: *grammar::ExprParser::new()
                .parse(code)
                .map_err(|e| ExprError::ParseError(e.to_string()))?,
        })
    }

    /// Run a compiled expr program
    pub fn run<K, V>(&self, program: ExprProgram, ctx: impl IntoIterator<Item=(K, V)>) -> Result<ExprValue>
    where
        K: AsRef<str>,
        V: Into<ExprValue>,
    {
        let ctx = ctx.into_iter().map(|(k, v)| (k.as_ref().to_string(), v.into())).collect();
        self.parse(program.expr, ctx)
    }

    /// Compile and run an expr program in one step
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::ExprParser;
    /// let p = ExprParser::default();
    /// let ctx: HashMap<String, String> = HashMap::new();
    /// assert_eq!(p.eval("1 + 2", ctx).unwrap().to_string(), "3");
    /// ```
    pub fn eval<K, V>(&self, code: &str, ctx: impl IntoIterator<Item=(K, V)>) -> Result<ExprValue>
    where
        K: AsRef<str>,
        V: Into<ExprValue>,
    {
        let program = self.compile(code)?;
        self.run(program, ctx)
    }

    fn parse(&self, expr: Expr, ctx: IndexMap<String, ExprValue>) -> Result<ExprValue> {
        let parse = |expr| self.parse(expr, ctx.clone());
        let value: ExprValue = match expr {
            Expr::Number(n) => n.into(),
            Expr::String(s) => s.into(),
            Expr::Bool(b) => b.into(),
            Expr::Float(f) => f.into(),
            Expr::Nil => ExprValue::Nil,
            Expr::ID(id) => {
                if let Some(value) = ctx.get(&id) {
                    value.clone()
                } else {
                    bail!("Unknown variable: {id}")
                }
            }
            Expr::Array(a) => a
                .into_iter()
                .map(|e| parse(*e))
                .collect::<Result<Vec<ExprValue>>>()?
                .into(),
            Expr::Map(m) => m
                .into_iter()
                .map(|(k, v)| Ok((k, parse(*v)?)))
                .collect::<Result<IndexMap<String, ExprValue>>>()?
                .into(),
            Expr::Func(name, args) => {
                let args = args
                    .into_iter()
                    .map(|e| parse(*e))
                    .collect::<Result<Vec<_>>>()?;
                if let Some(f) = self.functions.get(&name) {
                    f(&args)?
                } else {
                    bail!("Unknown function: {name}")
                }
            }
            Expr::Not(expr) => match parse(*expr)? {
                ExprValue::Bool(b) => (!b).into(),
                ExprValue::Nil => true.into(),
                value => bail!("Invalid operand for !: {value:?}"),
            },
            Expr::Ternary(cond, then, el) => match parse(*cond)? {
                ExprValue::Bool(true) => parse(*then)?,
                ExprValue::Bool(false) => parse(*el)?,
                value => bail!("Invalid condition for ?: {value:?}"),
            }
            Expr::NilCoalesce(lhs, rhs) => match parse(*lhs)? {
                ExprValue::Nil => parse(*rhs)?,
                value => value,
            },
            Expr::Slice(arr, lhs, rhs) => match parse(*arr)? {
                ExprValue::Array(mut a) => {
                    let lhs = match parse(*lhs)? {
                        ExprValue::Number(n) => n,
                        ExprValue::Nil => 0,
                        lhs => bail!("Invalid left-hand side of [{lhs:?}:{rhs:?}]"),
                    };
                    let rhs = match parse(*rhs)? {
                        ExprValue::Number(n) => n,
                        ExprValue::Nil => a.len() as i32,
                        rhs => bail!("Invalid right-hand side of [{lhs:?}:{rhs:?}]"),
                    };
                    let len = a.len() as i32;
                    let lhs = if lhs < 0 {
                        if lhs >= -len {
                            (len + lhs) as usize
                        } else {
                            0
                        }
                    } else {
                        lhs as usize
                    };
                    let rhs = if rhs < 0 {
                        if rhs >= -len {
                            (len + rhs) as usize
                        } else {
                            0
                        }
                    } else {
                        rhs as usize
                    };
                    ExprValue::Array(a.drain(lhs..rhs).collect())
                }
                arr => bail!("Invalid operands for [: {arr:?}, {lhs:?}, {rhs:?}"),
            },
            Expr::Pipe(lhs, rhs) => match (parse(*lhs)?, *rhs) {
                (lhs, Expr::Func(name, args)) => {
                    if let Some(f) = self.functions.get(&name) {
                        let args = args
                            .into_iter()
                            .map(|e| parse(*e))
                            .collect::<Result<Vec<ExprValue>>>()?
                            .into_iter()
                            .chain(once(lhs))
                            .collect();
                        f(&args)?
                    } else {
                        bail!("Unknown function: {name}")
                    }
                }
                _ => bail!("Invalid right-hand side of |"),
            },
            Expr::Op(lhs, op, rhs) => {
                let lhs = parse(*lhs)?;
                let rhs = parse(*rhs)?;
                match op {
                    Opcode::Add => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs + rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs + rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs + &rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for +: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Sub => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs - rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs - rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for -: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Mul => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs * rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs * rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for *: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Div => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs / rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs / rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for /: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Mod => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs % rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for %: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Pow => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => lhs.pow(rhs as u32).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => lhs.powf(rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for ^: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::And => match (lhs, rhs) {
                        (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs && rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for &&: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Or => match (lhs, rhs) {
                        (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs || rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for ||: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Eq => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs == rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs == rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs == rhs).into(),
                        (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs == rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for ==: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Ne => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs != rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs != rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs != rhs).into(),
                        (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs != rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for !=: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Lt => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs < rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs < rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs < rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for <: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Lte => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs <= rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs <= rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs <= rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for <=: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Gt => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs > rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs > rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs > rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for >: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Gte => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs >= rhs).into(),
                        (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs >= rhs).into(),
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs >= rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for >=: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Contains => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => lhs.contains(&rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for contains: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::StartsWith => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => lhs.starts_with(&rhs).into(),
                        (lhs, rhs) => {
                            bail!("Invalid operands for starts_with: {lhs:?} and {rhs:?}")
                        }
                    },
                    Opcode::EndsWith => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => lhs.ends_with(&rhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for ends_with: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Matches => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => regex::Regex::new(&rhs)?.is_match(&lhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for matches: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::In => match (lhs, rhs) {
                        (lhs, ExprValue::Array(rhs)) => rhs.contains(&lhs).into(),
                        (ExprValue::String(lhs), ExprValue::Map(rhs)) => rhs.contains_key(&lhs).into(),
                        (lhs, rhs) => bail!("Invalid operands for in: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Index => match (lhs, rhs) {
                        (ExprValue::Array(mut a), ExprValue::Number(n)) => {
                            if n < 0 {
                                if n >= -(a.len() as i32) {
                                    a.remove((a.len() as i32 + n) as usize)
                                } else {
                                    ExprValue::Nil
                                }
                            } else {
                                if n < a.len() as i32 {
                                    a.remove(n as usize)
                                } else {
                                    ExprValue::Nil
                                }
                            }
                        }
                        (ExprValue::Map(mut m), ExprValue::String(s)) => {
                            m.shift_remove(&s).unwrap_or(ExprValue::Nil)
                        }
                        (expr, index) => bail!("Invalid operands for []: {expr:?} and {index:?}"),
                    },
                    Opcode::OptIndex => match (lhs, rhs) {
                        (ExprValue::Map(mut m), ExprValue::String(s)) => {
                            m.shift_remove(&s).unwrap_or(ExprValue::Nil)
                        }
                        (ExprValue::Nil, _) => ExprValue::Nil,
                        (lhs, rhs) => bail!("Invalid operands for []?: {lhs:?} and {rhs:?}"),
                    },
                }
            }
        };
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_str_eq;
    use std::collections::HashMap;

    #[test]
    fn arithmetic() {
        assert_str_eq!(eval("2 + 3"), "5");
        assert_str_eq!(eval("2.1 + 3.2"), "5.300000000000001");
        assert_str_eq!(eval("2 - 3"), "-1");
        assert_str_eq!(eval("2.1 - 3.2"), "-1.1");
        assert_str_eq!(eval("2 * 3"), "6");
        assert_str_eq!(eval("2.1 * 3.2"), "6.720000000000001");
        assert_str_eq!(eval("7 / 3"), "2");
        assert_str_eq!(eval("7.0 / 3.0"), "2.3333333333333335");
        assert_str_eq!(eval("7 % 3"), "1");
        assert_str_eq!(eval("2 ** 3"), "8");
        assert_str_eq!(eval("2.0 ** 3.0"), "8");
        assert_str_eq!(eval("2 ^ 3"), "8");
        assert_str_eq!(eval("2.0 ^ 3.0"), "8");
        assert_str_eq!(eval("1 == 1"), "true");
        assert_str_eq!(eval("1 == 2"), "false");
        assert_str_eq!(eval("1 != 2"), "true");
        assert_str_eq!(eval("1 != 1"), "false");
    }

    #[test]
    fn string() {
        assert_str_eq!(eval(r#""foo" + "bar""#), r#""foobar""#);
        assert_str_eq!(eval(r#""foo" contains "o""#), "true");
        assert_str_eq!(eval(r#""foo" contains "x""#), "false");
        assert_str_eq!(eval(r#""foo" startsWith "f""#), "true");
        assert_str_eq!(eval(r#""foo" startsWith "x""#), "false");
        assert_str_eq!(eval(r#""foo" endsWith "o""#), "true");
        assert_str_eq!(eval(r#""foo" endsWith "x""#), "false");
        assert_str_eq!(eval(r#""foo" == "foo""#), "true");
        assert_str_eq!(eval(r#""foo" == "bar""#), "false");
        assert_str_eq!(eval(r#""foo" != "bar""#), "true");
        assert_str_eq!(eval(r#""foo" != "foo""#), "false");
        assert_str_eq!(eval(r#""bar" < "foo""#), "true");
        assert_str_eq!(eval(r#""foo" < "foo""#), "false");
        assert_str_eq!(eval(r#""foo" > "bar""#), "true");
        assert_str_eq!(eval(r#""foo" > "foo""#), "false");
        assert_str_eq!(eval(r#""bar" <= "foo""#), "true");
        assert_str_eq!(eval(r#""foo" <= "foo""#), "true");
        assert_str_eq!(eval(r#""bar" >= "foo""#), "false");
        assert_str_eq!(eval(r#""foo" >= "foo""#), "true");
        assert_str_eq!(eval(r#""foo" matches "^f""#), "true");
        assert_str_eq!(eval(r#""foo" matches "^x""#), "false");
        assert_str_eq!(
            eval(
                r#"`foo
bar`"#
            ),
            r#""foo\nbar""#
        );
    }

    #[test]
    fn nil() {
        assert_str_eq!(eval("nil"), "nil");
        assert_str_eq!(eval("!nil"), "true");
        assert_str_eq!(eval("!!nil"), "false");
    }

    #[test]
    fn logic() {
        assert_str_eq!(eval(r#"true && false"#), "false");
        assert_str_eq!(eval(r#"true || false"#), "true");
        assert_str_eq!(eval(r#"true == true"#), "true");
        assert_str_eq!(eval(r#"true == false"#), "false");
        assert_str_eq!(eval(r#"true != false"#), "true");
        assert_str_eq!(eval(r#"true != true"#), "false");
        assert_str_eq!(eval(r#"!true"#), "false");
        assert_str_eq!(eval(r#"not true"#), "false");
    }

    #[test]
    fn array() {
        assert_str_eq!(eval(r#"["foo","bar"]"#), r#"["foo", "bar"]"#);
        assert_str_eq!(eval(r#""foo" in ["foo", "bar"]"#), "true");
        assert_str_eq!(eval(r#""foo" in ["bar", "baz"]"#), "false");
        assert_str_eq!(eval(r#"["foo", "bar"][0]"#), r#""foo""#);
        assert_str_eq!(eval(r#"["foo", "bar"][1]"#), r#""bar""#);
        assert_str_eq!(eval(r#"["foo", "bar"][2]"#), "nil");
        assert_str_eq!(eval(r#"["foo", "bar"][-1]"#), r#""bar""#);
        assert_str_eq!(eval(r#"["foo", "bar"][0:1]"#), r#"["foo"]"#);
        assert_str_eq!(eval(r#"["foo", "bar"][0:2]"#), r#"["foo", "bar"]"#);
        assert_str_eq!(eval(r#"["foo", "bar"][0:-1]"#), r#"["foo"]"#);
        assert_str_eq!(eval(r#"["foo", "bar"][1:]"#), r#"["bar"]"#);
        assert_str_eq!(eval(r#"["foo", "bar"][:1]"#), r#"["foo"]"#);
        assert_str_eq!(eval(r#"["foo", "bar"][:]"#), r#"["foo", "bar"]"#);
    }

    #[test]
    fn map() {
        assert_str_eq!(eval(r#"{foo: "bar"}"#), r#"{foo: "bar"}"#);
        assert_str_eq!(eval(r#"{foo: "bar"}.foo"#), r#""bar""#);
        assert_str_eq!(eval(r#"{foo: "bar"}.baz"#), "nil");
        assert_str_eq!(eval(r#"{foo: "bar"}["foo"]"#), r#""bar""#);
        assert_str_eq!(eval(r#"{foo: "bar"}["baz"]"#), "nil");
        assert_str_eq!(eval(r#"{foo: "bar"}?.foo"#), r#""bar""#);
        assert_str_eq!(eval(r#"{foo: "bar"}?.bar?.foo"#), r#"nil"#);
        assert_str_eq!(eval(r#""foo" in {foo: "bar"}"#), "true");
        assert_str_eq!(eval(r#""bar" in {foo: "bar"}"#), "false");
    }

    #[test]
    fn context() {
        let ctx = [("Version", "v1.0.0")];
        let p = ExprParser::new();
        assert_str_eq!(p.eval(r#"Version matches "^v\\d+\\.\\d+\\.\\d+""#, ctx).unwrap().to_string(), "true");
    }

    #[test]
    fn functions() {
        let x = "s";
        let mut p = ExprParser::new();
        p.add_function("add", |args: &Vec<ExprValue>| -> Result<ExprValue> {
            eprintln!("{}", x);
            let mut sum = 0;
            for arg in args {
                if let ExprValue::Number(n) = arg {
                    sum += n;
                } else {
                    return Err(format!("Invalid argument: {arg:?}").into());
                }
            }
            Ok(sum.into())
        });
        let ctx: HashMap<String, String> = HashMap::new();
        assert_str_eq!(p.eval("add(1, 2, 3)", &ctx).unwrap().to_string(), "6");
        assert_str_eq!(p.eval("3 | add(1, 2)", &ctx).unwrap().to_string(), "6");
    }

    #[test]
    fn ternary() {
        assert_str_eq!(eval("true ? 1 : 2"), "1");
        assert_str_eq!(eval("false ? 1 : 2"), "2");
    }

    #[test]
    fn nil_coalesce() {
        assert_str_eq!(eval("nil ?? 1"), "1");
        assert_str_eq!(eval("2 ?? 1"), "2");
    }

    fn eval(code: &str) -> String {
        let ctx: HashMap<String, String> = HashMap::new();
        let p = ExprParser::new();
        p.eval(code, ctx)
            .map_err(|e| format!("code: {code}\n{e}"))
            .unwrap()
            .to_string()
    }
}
