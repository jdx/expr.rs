use crate::ast::node::Node;
use crate::ast::program::Program;
use crate::functions::{array, string, ExprCall, Function};
use crate::{ExprPest, Rule};
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
        Ok(value)
    }
}
