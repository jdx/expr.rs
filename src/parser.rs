use crate::ast::node::Node;
use crate::ast::program::Program;
use crate::functions::{array, string, ExprCall, Function};
use crate::pest::{ExprPest, Rule};
use crate::{bail, Context, Error, Result, Value};
use indexmap::IndexMap;
use pest::Parser as PestParser;
use std::fmt;
use std::fmt::{Debug, Formatter};

/// Main struct for parsing and evaluating expr programs
///
/// Example:
///
/// ```
/// use expr::{Context, Parser};
/// let ctx = Context::from_iter([("foo", 1), ("bar", 2)]);
/// let p = Parser::new();
/// assert_eq!(p.eval("foo + bar", &ctx).unwrap().to_string(), "3");
/// ```
#[derive(Default)]
pub struct Parser<'a> {
    pub(crate) functions: IndexMap<String, Function<'a>>,
}

impl Debug for Parser<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("ExprParser").finish()
    }
}

impl<'a> Parser<'a> {
    /// Create a new parser with default set of functions
    pub fn new() -> Self {
        let mut p = Self {
            functions: IndexMap::new(),
        };
        string::add_string_functions(&mut p);
        array::add_array_functions(&mut p);
        p
    }

    /// Add a function for expr programs to call
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{Context, Parser, Value};
    ///
    /// let mut p = Parser::new();
    /// let ctx = Context::default();
    /// p.add_function("add", |c| {
    ///   let mut sum = 0;
    ///     for arg in c.args {
    ///       if let Value::Number(n) = arg {
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
        F: Fn(ExprCall) -> Result<Value> + 'a + Sync + Send,
    {
        self.functions.insert(name.to_string(), Box::new(f));
    }

    /// Parse an expr program to be run later
    pub fn compile(&self, code: &str) -> Result<Program> {
        #[cfg(debug_assertions)]
        pest::set_error_detail(true);
        let pairs = ExprPest::parse(Rule::full, code).map_err(|e| Error::PestError(Box::new(e)))?;
        Ok(pairs.into())
    }

    /// Run a compiled expr program
    pub fn run(&self, program: Program, ctx: &Context) -> Result<Value> {
        let mut ctx = ctx.clone();
        ctx.insert("$env".to_string(), Value::Map(ctx.0.clone()));
        for (id, expr) in program.lines {
            ctx.insert(id, self.eval_expr(&ctx, expr)?);
        }
        self.eval_expr(&ctx, program.expr)
    }

    /// Compile and run an expr program in one step
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{Context, Parser};
    /// let p = Parser::default();
    /// let ctx = Context::default();
    /// assert_eq!(p.eval("1 + 2", &ctx).unwrap().to_string(), "3");
    /// ```
    pub fn eval(&self, code: &str, ctx: &Context) -> Result<Value> {
        let program = self.compile(code)?;
        self.run(program, ctx)
    }

    pub fn eval_expr(&self, ctx: &Context, node: Node) -> Result<Value> {
        let value = match node {
            Node::Value(value) => value,
            Node::Ident(id) => {
                if let Some(value) = ctx.get(&id) {
                    value.clone()
                } else if let Some(item) = ctx
                    .get("#")
                    .and_then(|o| o.as_map())
                    .and_then(|m| m.get(&id))
                {
                    item.clone()
                } else {
                    bail!("Unknown variable: {id}")
                }
            }
            Node::Func {
                ident,
                args,
                predicate,
            } => {
                let args = args
                    .into_iter()
                    .map(|e| self.eval_expr(ctx, e))
                    .collect::<Result<_>>()?;
                self.exec_func(ctx, ident, args, predicate.map(|l| *l))?
            },
            Node::Operation {
                left,
                operator,
                right,
            } => self.eval_operator(ctx, operator, *left, *right)?,
            Node::Unary { operator, node } => self.eval_unary_operator(ctx, operator, *node)?,
            Node::Postfix { operator, node } => self.eval_postfix_operator(ctx, operator, *node)?,
            Node::Array(a) => Value::Array(
                a.into_iter()
                    .map(|e| self.eval_expr(ctx, e))
                    .collect::<Result<_>>()?,
            ), // node => bail!("unexpected node: {node:?}"),
            Node::Range(start, end) => match (self.eval_expr(ctx, *start)?, self.eval_expr(ctx, *end)?) {
                (Value::Number(start), Value::Number(end)) => {
                    Value::Array((start..=end).map(Value::Number).collect())
                }
                (start, end) => bail!("Invalid range: {start:?}..{end:?}"),
            }
        };
        // let parse = |expr| self.parse(expr, ctx);
        // let value: ExprValue = match expr {
        //     Expr::Number(n) => n.into(),
        //     Expr::String(s) => s.into(),
        //     Expr::Bool(b) => b.into(),
        //     Expr::Float(f) => f.into(),
        //     Expr::Nil => ExprValue::Nil,
        //     Expr::ID(id) => {
        //         if let Some(value) = ctx.get(&id) {
        //             value.clone()
        //         } else {
        //             bail!("Unknown variable: {id}")
        //         }
        //     }
        //     Expr::Array(a) => a
        //         .into_iter()
        //         .map(|e| parse(*e))
        //         .collect::<Result<Vec<ExprValue>>>()?
        //         .into(),
        //     Expr::Map(m) => m
        //         .into_iter()
        //         .map(|(k, v)| Ok((k, parse(*v)?)))
        //         .collect::<Result<IndexMap<String, ExprValue>>>()?
        //         .into(),
        //     Expr::Func(func) => self.exec_func(ctx, func)?,
        //     Expr::Not(expr) => match parse(*expr)? {
        //         ExprValue::Bool(b) => (!b).into(),
        //         ExprValue::Nil => true.into(),
        //         value => bail!("Invalid operand for !: {value:?}"),
        //     },
        //     Expr::Ternary(cond, then, el) => match parse(*cond)? {
        //         ExprValue::Bool(true) => parse(*then)?,
        //         ExprValue::Bool(false) => parse(*el)?,
        //         value => bail!("Invalid condition for ?: {value:?}"),
        //     },
        //     Expr::NilCoalesce(lhs, rhs) => match parse(*lhs)? {
        //         ExprValue::Nil => parse(*rhs)?,
        //         value => value,
        //     },
        //     Expr::Slice(arr, lhs, rhs) => match parse(*arr)? {
        //         ExprValue::Array(mut a) => {
        //             let lhs = match parse(*lhs)? {
        //                 ExprValue::Number(n) => n,
        //                 ExprValue::Nil => 0,
        //                 lhs => bail!("Invalid left-hand side of [{lhs:?}:{rhs:?}]"),
        //             };
        //             let rhs = match parse(*rhs)? {
        //                 ExprValue::Number(n) => n,
        //                 ExprValue::Nil => a.len() as i64,
        //                 rhs => bail!("Invalid right-hand side of [{lhs:?}:{rhs:?}]"),
        //             };
        //             let len = a.len() as i64;
        //             let lhs = if lhs < 0 {
        //                 if lhs >= -len {
        //                     (len + lhs) as usize
        //                 } else {
        //                     0
        //                 }
        //             } else {
        //                 lhs as usize
        //             };
        //             let rhs = if rhs < 0 {
        //                 if rhs >= -len {
        //                     (len + rhs) as usize
        //                 } else {
        //                     0
        //                 }
        //             } else {
        //                 rhs as usize
        //             };
        //             ExprValue::Array(a.drain(lhs..rhs).collect())
        //         }
        //         arr => bail!("Invalid operands for [: {arr:?}, {lhs:?}, {rhs:?}"),
        //     },
        //     Expr::Pipe(lhs, mut func) => {
        //         func.1.push(lhs);
        //         self.exec_func(ctx, func)?
        //     }
        //     Expr::Op(lhs, op, rhs) => {
        //         let lhs = parse(*lhs)?;
        //         let rhs = parse(*rhs)?;
        //         match op {
        //             Opcode::Add => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs + rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs + rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs + &rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for +: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Sub => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs - rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs - rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for -: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Mul => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs * rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs * rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for *: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Div => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs / rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs / rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for /: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Mod => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs % rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for %: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Pow => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => {
        //                     lhs.pow(rhs as u32).into()
        //                 }
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => lhs.powf(rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for ^: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::And => match (lhs, rhs) {
        //                 (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs && rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for &&: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Or => match (lhs, rhs) {
        //                 (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs || rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for ||: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Eq => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs == rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs == rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs == rhs).into(),
        //                 (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs == rhs).into(),
        //                 (ExprValue::Array(lhs), ExprValue::Array(rhs)) => (lhs == rhs).into(),
        //                 (ExprValue::Map(lhs), ExprValue::Map(rhs)) => (lhs == rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for ==: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Ne => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs != rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs != rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs != rhs).into(),
        //                 (ExprValue::Bool(lhs), ExprValue::Bool(rhs)) => (lhs != rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for !=: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Lt => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs < rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs < rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs < rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for <: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Lte => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs <= rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs <= rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs <= rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for <=: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Gt => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs > rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs > rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs > rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for >: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Gte => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs >= rhs).into(),
        //                 (ExprValue::Float(lhs), ExprValue::Float(rhs)) => (lhs >= rhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => (lhs >= rhs).into(),
        //                 (lhs, rhs) => bail!("Invalid operands for >=: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Contains => match (lhs, rhs) {
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => {
        //                     lhs.contains(&rhs).into()
        //                 }
        //                 (lhs, rhs) => bail!("Invalid operands for contains: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::StartsWith => match (lhs, rhs) {
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => {
        //                     lhs.starts_with(&rhs).into()
        //                 }
        //                 (lhs, rhs) => {
        //                     bail!("Invalid operands for starts_with: {lhs:?} and {rhs:?}")
        //                 }
        //             },
        //             Opcode::EndsWith => match (lhs, rhs) {
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => {
        //                     lhs.ends_with(&rhs).into()
        //                 }
        //                 (lhs, rhs) => bail!("Invalid operands for ends_with: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Matches => match (lhs, rhs) {
        //                 (ExprValue::String(lhs), ExprValue::String(rhs)) => {
        //                     regex::Regex::new(&rhs)?.is_match(&lhs).into()
        //                 }
        //                 (lhs, rhs) => bail!("Invalid operands for matches: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Range => match (lhs, rhs) {
        //                 (ExprValue::Number(lhs), ExprValue::Number(rhs)) => (lhs..=rhs)
        //                     .map(ExprValue::Number)
        //                     .collect::<Vec<_>>()
        //                     .into(),
        //                 (lhs, rhs) => bail!("Invalid operands for ..: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::In => match (lhs, rhs) {
        //                 (lhs, ExprValue::Array(rhs)) => rhs.contains(&lhs).into(),
        //                 (ExprValue::String(lhs), ExprValue::Map(rhs)) => {
        //                     rhs.contains_key(&lhs).into()
        //                 }
        //                 (lhs, rhs) => bail!("Invalid operands for in: {lhs:?} and {rhs:?}"),
        //             },
        //             Opcode::Index => match (lhs, rhs) {
        //                 (ExprValue::Array(mut a), ExprValue::Number(n)) => {
        //                     if n < 0 {
        //                         if n >= -(a.len() as i64) {
        //                             a.remove((a.len() as i64 + n) as usize)
        //                         } else {
        //                             ExprValue::Nil
        //                         }
        //                     } else {
        //                         if n < a.len() as i64 {
        //                             a.remove(n as usize)
        //                         } else {
        //                             ExprValue::Nil
        //                         }
        //                     }
        //                 }
        //                 (ExprValue::Map(mut m), ExprValue::String(s)) => {
        //                     m.shift_remove(&s).unwrap_or(ExprValue::Nil)
        //                 }
        //                 (expr, index) => bail!("Invalid operands for []: {expr:?} and {index:?}"),
        //             },
        //             Opcode::OptIndex => match (lhs, rhs) {
        //                 (ExprValue::Map(mut m), ExprValue::String(s)) => {
        //                     m.shift_remove(&s).unwrap_or(ExprValue::Nil)
        //                 }
        //                 (ExprValue::Nil, _) => ExprValue::Nil,
        //                 (lhs, rhs) => bail!("Invalid operands for []?: {lhs:?} and {rhs:?}"),
        //             },
        //         }
        //     }
        // };
        Ok(value)
    }
}
