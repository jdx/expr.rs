//! Implementation of [expr](https://expr-lang.org) in rust
//!
//! Example:
//! ```
//! use std::collections::HashMap;
//! use expr::{ExprContext, ExprParser};
//! let p = ExprParser::new();
//! let ctx = ExprContext::default();
//! assert_eq!(p.eval("1 + 2", &ctx).unwrap().to_string(), "3");
//! ```

use indexmap::IndexMap;
use lalrpop_util::lalrpop_mod;
use std::fmt;
use std::fmt::{Debug, Formatter};

mod error;
mod context;
mod value;

pub use error::ExprError;
use error::Result;
pub use crate::context::ExprContext;
pub use crate::value::ExprValue;

type Function<'a> = Box<dyn Fn(ExprCall) -> Result<ExprValue> + 'a + Sync + Send>;

/// A parsed expr program that can be run
#[derive(Debug, Clone)]
pub struct ExprProgram {
    lines: Vec<(String, Box<Expr>)>,
    expr: Box<Expr>,
}

pub struct ExprCall<'a, 'b> {
    pub name: String,
    pub args: Vec<ExprValue>,
    pub predicate: Option<ExprProgram>,
    pub ctx: &'a ExprContext,
    pub parser: &'a ExprParser<'b>,
}

#[derive(Debug, Clone)]
enum Expr {
    Number(i64),
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
    Func(Func),
    Pipe(Box<Expr>, Func),
}

#[derive(Debug, Clone)]
struct Func(String, Vec<Box<Expr>>, Option<ExprProgram>);

impl Expr {
    pub fn unescape_str(s: &str) -> Self {
        Expr::String(
            s.replace("\\\\", "\\")
                .replace("\\n", "\n")
                .replace("\\r", "\r")
                .replace("\\t", "\t")
                .replace("\\\"", "\""),
        )
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
    Range,
}

/// Main struct for parsing and evaluating expr programs
///
/// Example:
///
/// ```
/// use expr::{ExprContext, ExprParser};
/// let ctx = ExprContext::from_iter([("foo", 1), ("bar", 2)]);
/// let p = ExprParser::new();
/// assert_eq!(p.eval("foo + bar", &ctx).unwrap().to_string(), "3");
/// ```
#[derive(Default)]
pub struct ExprParser<'a> {
    functions: IndexMap<String, Function<'a>>,
}

impl Debug for ExprParser<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("ExprParser").finish()
    }
}

lalrpop_mod!(grammar);

impl<'a> ExprParser<'a> {
    /// Create a new parser with default set of functions
    pub fn new() -> Self {
        let mut p = Self {
            functions: IndexMap::new(),
        };

        p.add_function("filter", |c| {
            let mut result = Vec::new();
            if c.args.len() != 1 {
                bail!("filter() takes exactly one argument and a predicate");
            }
            if let (ExprValue::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
                for value in a {
                    let mut ctx = c.ctx.clone();
                    ctx.insert("#".to_string(), value.clone());
                    if let ExprValue::Bool(true) = c.parser.run(predicate.clone(), &ctx)? {
                        result.push(value.clone());
                    }
                }
            } else {
                bail!("filter() takes an array as the first argument");
            }
            Ok(result.into())
        });

        p.add_function("trim", |c| {
            if c.args.len() != 1 && c.args.len() != 2 {
                bail!("trim() takes one or two arguments");
            }
            if let (ExprValue::String(s), None) = (&c.args[0], c.args.get(1)) {
                Ok(s.trim().into())
            } else if let (ExprValue::String(s), Some(ExprValue::String(chars))) = (&c.args[0], c.args.get(1)) {
                Ok(s.trim_matches(|c| chars.contains(c)).into())
            } else {
                bail!("trim() takes a string as the first argument and an optional string of characters to trim");
            }
        });

        p.add_function("trimPrefix", |c| {
            if let (ExprValue::String(s), ExprValue::String(prefix)) = (&c.args[0], &c.args[1]) {
                Ok(s.strip_prefix(prefix).unwrap_or(s).into())
            } else {
                bail!("trimPrefix() takes a string as the first argument and a string to trim as the second argument");
            }
        });

        p.add_function("trimSuffix", |c| {
            if let (ExprValue::String(s), ExprValue::String(suffix)) = (&c.args[0], &c.args[1]) {
                Ok(s.strip_suffix(suffix).unwrap_or(s).into())
            } else {
                bail!("trimSuffix() takes a string as the first argument and a string to trim as the second argument");
            }
        });

        p.add_function("upper", |c| {
            if c.args.len() != 1 {
                bail!("upper() takes one argument");
            }
            if let ExprValue::String(s) = &c.args[0] {
                Ok(s.to_uppercase().into())
            } else {
                bail!("upper() takes a string as the first argument");
            }
        });

        p.add_function("lower", |c| {
            if c.args.len() != 1 {
                bail!("lower() takes one argument");
            }
            if let ExprValue::String(s) = &c.args[0] {
                Ok(s.to_lowercase().into())
            } else {
                bail!("lower() takes a string as the first argument");
            }
        });

        p.add_function("split", |c| {
            if let (ExprValue::String(s), ExprValue::String(sep), None) = (&c.args[0], &c.args[1], c.args.get(2)) {
                Ok(s.split(sep).map(|s| ExprValue::from(s)).collect::<Vec<_>>().into())
            } else if let (ExprValue::String(s), ExprValue::String(sep), Some(ExprValue::Number(n))) = (&c.args[0], &c.args[1], c.args.get(2)) {
                Ok(s.splitn(*n as usize, sep).map(|s| ExprValue::from(s)).collect::<Vec<_>>().into())
            } else {
                bail!("split() takes a string as the first argument and a string as the second argument");
            }
        });

        p.add_function("splitAfter", |c| {
            if let (ExprValue::String(s), ExprValue::String(sep), None) = (&c.args[0], &c.args[1], c.args.get(2)) {
                Ok(s.split_inclusive(sep).map(|s| ExprValue::from(s)).collect::<Vec<_>>().into())
            } else if let (ExprValue::String(s), ExprValue::String(sep), Some(ExprValue::Number(n))) = (&c.args[0], &c.args[1], c.args.get(2)) {
                let mut arr = s.split_inclusive(sep).take(*n as usize - 1).map(|s| s.to_string()).collect::<Vec<_>>();
                arr.push(s.split_inclusive(sep).skip(*n as usize - 1).collect::<Vec<_>>().join(""));
                Ok(arr.into())
            } else {
                bail!("splitAfter() takes a string as the first argument and a string as the second argument");
            }
        });

        p.add_function("replace", |c| {
            if let (ExprValue::String(s), ExprValue::String(from), ExprValue::String(to)) = (&c.args[0], &c.args[1], &c.args[2]) {
                Ok(s.replace(from, to).into())
            } else {
                bail!("replace() takes a string as the first argument and two strings to replace");
            }
        });

        p.add_function("repeat", |c| {
            if let (ExprValue::String(s), ExprValue::Number(n)) = (&c.args[0], &c.args[1]) {
                Ok(s.repeat(*n as usize+1).into())
            } else {
                bail!("repeat() takes a string as the first argument and a number as the second argument");
            }
        });

        p.add_function("indexOf", |c| {
            if let (ExprValue::String(s), ExprValue::String(sub)) = (&c.args[0], &c.args[1]) {
                Ok(s.find(sub).map(|i| i as i64).unwrap_or(-1).into())
            } else {
                bail!("indexOf() takes a string as the first argument and a string to search for as the second argument");
            }
        });

        p.add_function("lastIndexOf", |c| {
            if let (ExprValue::String(s), ExprValue::String(sub)) = (&c.args[0], &c.args[1]) {
                Ok(s.rfind(sub).map(|i| i as i64).unwrap_or(-1).into())
            } else {
                bail!("lastIndexOf() takes a string as the first argument and a string to search for as the second argument");
            }
        });

        p.add_function("hasPrefix", |c| {
            if let (ExprValue::String(s), ExprValue::String(prefix)) = (&c.args[0], &c.args[1]) {
                Ok(s.starts_with(prefix).into())
            } else {
                bail!("hasPrefix() takes a string as the first argument and a string to search for as the second argument");
            }
        });

        p.add_function("hasSuffix", |c| {
            if let (ExprValue::String(s), ExprValue::String(suffix)) = (&c.args[0], &c.args[1]) {
                Ok(s.ends_with(suffix).into())
            } else {
                bail!("hasSuffix() takes a string as the first argument and a string to search for as the second argument");
            }
        });

        p
    }

    /// Add a function for expr programs to call
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{ExprContext, ExprParser, ExprValue};
    ///
    /// let mut p = ExprParser::new();
    /// let ctx = ExprContext::default();
    /// p.add_function("add", |c| {
    ///   let mut sum = 0;
    ///     for arg in c.args {
    ///       if let ExprValue::Number(n) = arg {
    ///         sum += n;
    ///        } else {
    ///          panic!("Invalid argument: {arg:?}");
    ///        }
    ///     }
    ///   Ok(sum.into())
    /// });
    /// assert_eq!(p.eval("add(1, 2, 3)", &ctx).unwrap().to_string(), "6");
    /// ```
    pub fn add_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(ExprCall) -> Result<ExprValue> + 'a + Sync + Send,
    {
        self.functions.insert(name.to_string(), Box::new(f));
    }

    /// Parse an expr program to be run later
    pub fn compile(&self, code: &str) -> Result<ExprProgram> {
        grammar::ProgramParser::new()
            .parse(code)
            .map_err(|e| ExprError::ParseError(e.to_string()))
    }

    /// Run a compiled expr program
    pub fn run(&self, program: ExprProgram, ctx: &ExprContext) -> Result<ExprValue> {
        let mut ctx = ctx.clone();
        ctx.insert("$env".to_string(), ExprValue::Map(ctx.0.clone()));
        for (id, expr) in program.lines {
            ctx.insert(id, self.parse(*expr, &ctx)?);
        }
        self.parse(*program.expr, &ctx)
    }

    /// Compile and run an expr program in one step
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{ExprContext, ExprParser};
    /// let p = ExprParser::default();
    /// let ctx = ExprContext::default();
    /// assert_eq!(p.eval("1 + 2", &ctx).unwrap().to_string(), "3");
    /// ```
    pub fn eval(&self, code: &str, ctx: &ExprContext) -> Result<ExprValue> {
        let program = self.compile(code)?;
        self.run(program, ctx)
    }

    fn parse(&self, expr: Expr, ctx: &ExprContext) -> Result<ExprValue> {
        let parse = |expr| self.parse(expr, ctx);
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
            Expr::Func(func) => self.exec_func(ctx, func)?,
            Expr::Not(expr) => match parse(*expr)? {
                ExprValue::Bool(b) => (!b).into(),
                ExprValue::Nil => true.into(),
                value => bail!("Invalid operand for !: {value:?}"),
            },
            Expr::Ternary(cond, then, el) => match parse(*cond)? {
                ExprValue::Bool(true) => parse(*then)?,
                ExprValue::Bool(false) => parse(*el)?,
                value => bail!("Invalid condition for ?: {value:?}"),
            },
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
                        ExprValue::Nil => a.len() as i64,
                        rhs => bail!("Invalid right-hand side of [{lhs:?}:{rhs:?}]"),
                    };
                    let len = a.len() as i64;
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
            Expr::Pipe(lhs, mut func) => {
                func.1.push(lhs);
                self.exec_func(ctx, func)?
            }
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
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => {
                            lhs.pow(rhs as u32).into()
                        }
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
                        (ExprValue::Array(lhs), ExprValue::Array(rhs)) => (lhs == rhs).into(),
                        (ExprValue::Map(lhs), ExprValue::Map(rhs)) => (lhs == rhs).into(),
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
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => {
                            lhs.contains(&rhs).into()
                        }
                        (lhs, rhs) => bail!("Invalid operands for contains: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::StartsWith => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => {
                            lhs.starts_with(&rhs).into()
                        }
                        (lhs, rhs) => {
                            bail!("Invalid operands for starts_with: {lhs:?} and {rhs:?}")
                        }
                    },
                    Opcode::EndsWith => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => {
                            lhs.ends_with(&rhs).into()
                        }
                        (lhs, rhs) => bail!("Invalid operands for ends_with: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Matches => match (lhs, rhs) {
                        (ExprValue::String(lhs), ExprValue::String(rhs)) => {
                            regex::Regex::new(&rhs)?.is_match(&lhs).into()
                        }
                        (lhs, rhs) => bail!("Invalid operands for matches: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Range => match (lhs, rhs) {
                        (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs..=rhs)
                            .map(ExprValue::Number)
                            .collect::<Vec<_>>()
                            .into(),
                        (lhs, rhs) => bail!("Invalid operands for ..: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::In => match (lhs, rhs) {
                        (lhs, ExprValue::Array(rhs)) => rhs.contains(&lhs).into(),
                        (ExprValue::String(lhs), ExprValue::Map(rhs)) => {
                            rhs.contains_key(&lhs).into()
                        }
                        (lhs, rhs) => bail!("Invalid operands for in: {lhs:?} and {rhs:?}"),
                    },
                    Opcode::Index => match (lhs, rhs) {
                        (ExprValue::Array(mut a), ExprValue::Number(n)) => {
                            if n < 0 {
                                if n >= -(a.len() as i64) {
                                    a.remove((a.len() as i64 + n) as usize)
                                } else {
                                    ExprValue::Nil
                                }
                            } else {
                                if n < a.len() as i64 {
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

    fn exec_func(&self, ctx: &ExprContext, func: Func) -> Result<ExprValue> {
        let Func(name, args, predicate) = func;
        let args = args
            .into_iter()
            .map(|e| self.parse(*e, ctx))
            .collect::<Result<Vec<_>>>()?;
        let call = ExprCall {
            name,
            args,
            predicate,
            ctx,
            parser: self,
        };
        if let Some(f) = self.functions.get(&call.name) {
            f(call)
        } else {
            bail!("Unknown function: {}", call.name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_str_eq;

    macro_rules! test {
        ($code:expr, $expected:expr) => {{
            let ctx = ExprContext::default();
            let p = ExprParser::new();
            let code = $code;
            let result = p.eval(code, &ctx)
                .map_err(|e| ExprError::from(format!("{code}: {e}")))
                .map(|v| v.to_string())?;
            assert_str_eq!(result, $expected);
        }};
    }

    #[test]
    fn arithmetic() -> Result<()> {
        test!("2 + 3", "5");
        test!("2 + 3", "5");
        test!("2.1 + 3.2", "5.300000000000001");
        test!("2 - 3", "-1");
        test!("2.1 - 3.2", "-1.1");
        test!("2 * 3", "6");
        test!("2.1 * 3.2", "6.720000000000001");
        test!("7 / 3", "2");
        test!("7.0 / 3.0", "2.3333333333333335");
        test!("7 % 3", "1");
        test!("2 ** 3", "8");
        test!("2.0 ** 3.0", "8");
        test!("2 ^ 3", "8");
        test!("2.0 ^ 3.0", "8");
        test!("1 == 1", "true");
        test!("1 == 2", "false");
        test!("1 != 2", "true");
        test!("1 != 1", "false");
        Ok(())
    }

    #[test]
    fn string() -> Result<()> {
        test!(r#""foo" + "bar""#, r#""foobar""#);
        test!(r#""foo" contains "o""#, "true");
        test!(r#""foo" contains "x""#, "false");
        test!(r#""foo" startsWith "f""#, "true");
        test!(r#""foo" startsWith "x""#, "false");
        test!(r#""foo" endsWith "o""#, "true");
        test!(r#""foo" endsWith "x""#, "false");
        test!(r#""foo" == "foo""#, "true");
        test!(r#""foo" == "bar""#, "false");
        test!(r#""foo" != "bar""#, "true");
        test!(r#""foo" != "foo""#, "false");
        test!(r#""bar" < "foo""#, "true");
        test!(r#""foo" < "foo""#, "false");
        test!(r#""foo" > "bar""#, "true");
        test!(r#""foo" > "foo""#, "false");
        test!(r#""bar" <= "foo""#, "true");
        test!(r#""foo" <= "foo""#, "true");
        test!(r#""bar" >= "foo""#, "false");
        test!(r#""foo" >= "foo""#, "true");
        test!(r#""foo" matches "^f""#, "true");
        test!(r#""foo" matches "^x""#, "false");
        test!(r#"`foo
bar`"#,r#""foo\nbar""#);
        Ok(())
    }

    #[test]
    fn nil() -> Result<()> {
        test!("nil", "nil");
        test!("!nil", "true");
        test!("!!nil", "false");
        Ok(())
    }

    #[test]
    fn logic() -> Result<()> {
        test!(r#"true && false"#, "false");
        test!(r#"true || false"#, "true");
        test!(r#"true == true"#, "true");
        test!(r#"true == false"#, "false");
        test!(r#"true != false"#, "true");
        test!(r#"true != true"#, "false");
        test!(r#"!true"#, "false");
        test!(r#"not true"#, "false");
        Ok(())
    }

    #[test]
    fn array() -> Result<()> {
        test!(r#"["foo","bar"]"#, r#"["foo", "bar"]"#);
        test!(r#""foo" in ["foo", "bar"]"#, "true");
        test!(r#""foo" in ["bar", "baz"]"#, "false");
        test!(r#"["foo", "bar"][0]"#, r#""foo""#);
        test!(r#"["foo", "bar"][1]"#, r#""bar""#);
        test!(r#"["foo", "bar"][2]"#, "nil");
        test!(r#"["foo", "bar"][-1]"#, r#""bar""#);
        test!(r#"["foo", "bar"][0:1]"#, r#"["foo"]"#);
        test!(r#"["foo", "bar"][0:2]"#, r#"["foo", "bar"]"#);
        test!(r#"["foo", "bar"][0:-1]"#, r#"["foo"]"#);
        test!(r#"["foo", "bar"][1:]"#, r#"["bar"]"#);
        test!(r#"["foo", "bar"][:1]"#, r#"["foo"]"#);
        test!(r#"["foo", "bar"][:]"#, r#"["foo", "bar"]"#);
        Ok(())
    }

    #[test]
    fn map() -> Result<()> {
        test!(r#"{foo: "bar"}"#, r#"{foo: "bar"}"#);
        test!(r#"{foo: "bar"}.foo"#, r#""bar""#);
        test!(r#"{foo: "bar"}.baz"#, "nil");
        test!(r#"{foo: "bar"}["foo"]"#, r#""bar""#);
        test!(r#"{foo: "bar"}["baz"]"#, "nil");
        test!(r#"{foo: "bar"}?.foo"#, r#""bar""#);
        test!(r#"{foo: "bar"}?.bar?.foo"#, r#"nil"#);
        test!(r#""foo" in {foo: "bar"}"#, "true");
        test!(r#""bar" in {foo: "bar"}"#, "false");
        Ok(())
    }

    #[test]
    fn context() -> Result<()> {
        let ctx = ExprContext::from_iter([("Version".to_string(), "v1.0.0".to_string())]);
        let p = ExprParser::new();
        assert_str_eq!(
            p.eval(r#"Version matches "^v\\d+\\.\\d+\\.\\d+""#, &ctx)?
                .to_string(),
            "true"
        );
        assert_str_eq!(p.eval(r#""Version" in $env"#, &ctx)?.to_string(), r#"true"#);
        assert_str_eq!(
            p.eval(r#""version" in $env"#, &ctx)?.to_string(),
            r#"false"#
        );
        assert_str_eq!(
            p.eval(r#"$env["Version"]"#, &ctx)?.to_string(),
            r#""v1.0.0""#
        );
        Ok(())
    }

    #[test]
    fn functions() -> Result<()> {
        let x = "s";
        let mut p = ExprParser::new();
        p.add_function("add", |c| -> Result<ExprValue> {
            eprintln!("{}", x);
            let mut sum = 0;
            for arg in c.args {
                if let ExprValue::Number(n) = arg {
                    sum += n;
                } else {
                    return Err(format!("Invalid argument: {arg:?}").into());
                }
            }
            Ok(sum.into())
        });
        let ctx = ExprContext::default();
        assert_str_eq!(p.eval("add(1, 2, 3)", &ctx)?.to_string(), "6");
        assert_str_eq!(p.eval("3 | add(1, 2)", &ctx)?.to_string(), "6");
        Ok(())
    }

    #[test]
    fn string_functions() -> Result<()> {
        test!("trim(\"  foo  \")", r#""foo""#);
        test!("trim(\"__foo__\", \"_\")", r#""foo""#);
        test!("trimPrefix(\"foo\", \"f\")", r#""oo""#);
        test!("trimSuffix(\"foo\", \"oo\")", r#""f""#);
        test!("upper(\"foo\")", r#""FOO""#);
        test!("lower(\"FOO\")", r#""foo""#);
        test!("split(\"foo,bar\", \",\")", r#"["foo", "bar"]"#);
        test!(r#"split("apple,orange,grape", ",", 2)"#, r#"["apple", "orange,grape"]"#);
        test!("splitAfter(\"foo,bar\", \",\")", r#"["foo,", "bar"]"#);
        test!(r#"splitAfter("apple,orange,grape", ",", 2)"#, r#"["apple,", "orange,grape"]"#);
        test!("replace(\"foo bar foo\", \"foo\", \"baz\")", r#""baz bar baz""#);
        test!(r#"repeat("Hi", 2)"#, r#""HiHiHi""#);
        test!("indexOf(\"foo bar foo\", \"bar\")", "4");
        test!("lastIndexOf(\"foo bar foo\", \"foo\")", "8");
        test!(r#"hasPrefix("HelloWorld", "Hello")"#, "true");
        test!(r#"hasSuffix("HelloWorld", "World")"#, "true");
        Ok(())
    }

    #[test]
    fn variables() -> Result<()> {
        test!("let x = 1; x", "1");
        Ok(())
    }

    #[test]
    fn ternary() -> Result<()> {
        test!("true ? 1 : 2", "1");
        test!("false ? 1 : 2", "2");
        Ok(())
    }

    #[test]
    fn nil_coalesce() -> Result<()> {
        test!("nil ?? 1", "1");
        test!("2 ?? 1", "2");
        Ok(())
    }

    #[test]
    fn range() -> Result<()> {
        test!("1..3 == [1, 2, 3]", "true");
        Ok(())
    }

    #[test]
    fn filter() -> Result<()> {
        test!("filter(0..9, {# % 2 == 0})", "[0, 2, 4, 6, 8]");
        Ok(())
    }
}
