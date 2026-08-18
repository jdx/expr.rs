use crate::ast::node::Node;
use crate::ast::program::Program;
use crate::functions::{ExprCall, Function, array, bitwise, convert, json, string};
use crate::parser::compile;
use crate::{Context, EvalContext, Result, Value, bail};
use indexmap::IndexMap;
use once_cell::sync::Lazy;
use std::fmt;
use std::fmt::{Debug, Formatter};

/// Run a compiled expr program, using the default environment
pub fn run(program: &Program, ctx: &Context) -> Result<Value> {
    DEFAULT_ENVIRONMENT.run(program, ctx)
}

/// Compile and run an expr program in one step, using the default environment.
///
/// Example:
/// ```
/// use expr::{Context, eval};
/// let ctx = Context::default();
/// assert_eq!(eval("1 + 2", &ctx).unwrap().to_string(), "3");
/// ```
pub fn eval(code: &str, ctx: &Context) -> Result<Value> {
    DEFAULT_ENVIRONMENT.eval(code, ctx)
}

/// Struct containing custom environment setup for expr evaluation (e.g. custom
/// function definitions)
///
/// Example:
///
/// ```
/// use expr::{Context, Environment, Value};
/// let mut env = Environment::new();
/// let ctx = Context::default();
/// env.add_function("add", |c| {
///   let mut sum = 0;
///     for arg in c.args {
///       if let Value::Integer(n) = arg {
///         sum += n;
///        } else {
///          panic!("Invalid argument: {arg:?}");
///        }
///     }
///   Ok(sum.into())
/// });
/// assert_eq!(env.eval("add(1, 2, 3)", &ctx).unwrap().to_string(), "6");
/// ```
#[derive(Default)]
pub struct Environment<'a> {
    pub(crate) functions: IndexMap<String, Function<'a>>,
}

impl Debug for Environment<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("ExprEnvironment").finish()
    }
}

impl<'a> Environment<'a> {
    /// Create a new environment with default set of functions
    pub fn new() -> Self {
        let mut p = Self {
            functions: IndexMap::new(),
        };
        string::add_string_functions(&mut p);
        array::add_array_functions(&mut p);
        bitwise::add_bitwise_functions(&mut p);
        convert::add_conversion_functions(&mut p);
        json::add_json_functions(&mut p);
        p
    }

    /// Add a function for expr programs to call
    ///
    /// Example:
    /// ```
    /// use expr::{Context, Environment, Value};
    /// let mut env = Environment::new();
    /// let ctx = Context::default();
    /// env.add_function("add", |c| {
    ///   let mut sum = 0;
    ///     for arg in c.args {
    ///       if let Value::Integer(n) = arg {
    ///         sum += n;
    ///        } else {
    ///          panic!("Invalid argument: {arg:?}");
    ///        }
    ///     }
    ///   Ok(sum.into())
    /// });
    /// assert_eq!(env.eval("add(1, 2, 3)", &ctx).unwrap().to_string(), "6");
    /// ```
    pub fn add_function<F>(&mut self, name: &str, f: F)
    where
        F: Fn(ExprCall) -> Result<Value> + 'a + Sync + Send,
    {
        self.functions.insert(name.to_string(), Box::new(f));
    }

    /// Run a compiled expr program
    pub fn run(&self, program: &Program, ctx: &Context) -> Result<Value> {
        let mut ctx = EvalContext::new(ctx);
        self.run_in_context(program, &mut ctx)
    }

    fn run_in_context(&self, program: &Program, ctx: &mut EvalContext) -> Result<Value> {
        for (id, expr) in &program.lines {
            ctx.insert(id.clone(), self.eval_node(ctx, expr)?);
        }
        self.eval_node(ctx, &program.expr)
    }

    pub(crate) fn run_with_binding(
        &self,
        program: &Program,
        parent: &EvalContext,
        key: &str,
        value: &Value,
    ) -> Result<Value> {
        let mut ctx = EvalContext::with_binding(parent, key, value);
        self.run_in_context(program, &mut ctx)
    }

    /// Compile and run an expr program in one step
    ///
    /// Example:
    /// ```
    /// use std::collections::HashMap;
    /// use expr::{Context, Environment};
    /// let env = Environment::new();
    /// let ctx = Context::default();
    /// assert_eq!(env.eval("1 + 2", &ctx).unwrap().to_string(), "3");
    /// ```
    pub fn eval(&self, code: &str, ctx: &Context) -> Result<Value> {
        let program = compile(code)?;
        self.run(&program, ctx)
    }

    pub fn eval_expr(&self, ctx: &Context, node: &Node) -> Result<Value> {
        let ctx = EvalContext::new(ctx);
        self.eval_node(&ctx, node)
    }

    pub(crate) fn eval_node(&self, ctx: &EvalContext, node: &Node) -> Result<Value> {
        let value = match node {
            Node::Value(value) => value.clone(),
            Node::Ident(id) => {
                if id == "$env" {
                    Value::Map(ctx.environment_context().0)
                } else if let Some(value) = ctx.get(id) {
                    value.clone()
                } else if let Some(item) = ctx
                    .get("#")
                    .and_then(|o| o.as_map())
                    .and_then(|m| m.get(id))
                {
                    item.clone()
                } else {
                    bail!("unknown variable: {id}")
                }
            }
            Node::Func {
                ident,
                args,
                predicate,
            } => {
                let args = args
                    .iter()
                    .map(|e| self.eval_node(ctx, e))
                    .collect::<Result<_>>()?;
                self.eval_func(ctx, ident, args, predicate.as_deref())?
            },
            Node::Operation {
                left,
                operator,
                right,
            } => self.eval_operator(ctx, operator, left, right)?,
            Node::Unary { operator, node } => self.eval_unary_operator(ctx, operator, node)?,
            Node::Postfix { operator, node } => self.eval_postfix_operator(ctx, operator, node)?,
            Node::Array(a) => Value::Array(
                a.iter()
                    .map(|e| self.eval_node(ctx, e))
                    .collect::<Result<_>>()?,
            ), // node => bail!("unexpected node: {node:?}"),
            Node::Range(start, end) => match (self.eval_node(ctx, start)?, self.eval_node(ctx, end)?) {
                (Value::Integer(start), Value::Integer(end)) => {
                    Value::Array((start..=end).map(Value::Integer).collect())
                }
                (start, end) => bail!("invalid range: {start:?}..{end:?}"),
            }
        };
        Ok(value)
    }
}

pub(crate) static DEFAULT_ENVIRONMENT: Lazy<Environment> = Lazy::new(|| {
    Environment::new()
});
