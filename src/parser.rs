use crate::ast::node::Node;
use crate::ast::program::Program;
use crate::eval::Environment;
use crate::functions::ExprCall;
use crate::{ContextProvider, Error, Result, Value};
use crate::{ExprPest, Rule};
use pest::Parser as PestParser;
use pest::iterators::Pairs;
use std::fmt;
use std::fmt::{Debug, Formatter};

/// Parse an expr program to be run later
pub fn compile(code: &str) -> Result<Program> {
    #[cfg(debug_assertions)]
    pest::set_error_detail(true);
    let pairs = ExprPest::parse(Rule::full, code).map_err(|e| Error::PestError(Box::new(e)))?;
    validate_numeric_literals(pairs.clone())?;
    Ok(pairs.into())
}

fn validate_numeric_literals(pairs: Pairs<'_, Rule>) -> Result<()> {
    for pair in pairs {
        match pair.as_rule() {
            Rule::int => {
                Value::parse_integer(pair.as_str()).map_err(|error| {
                    Error::ParseError(format!("invalid integer literal {}: {error}", pair.as_str()))
                })?;
            }
            Rule::decimal => {
                let value = Value::parse_float(pair.as_str()).map_err(|error| {
                    Error::ParseError(format!("invalid float literal {}: {error}", pair.as_str()))
                })?;
                if !value.is_finite() {
                    return Err(Error::ParseError(format!(
                        "float literal is out of range: {}",
                        pair.as_str()
                    )));
                }
            }
            _ => {}
        }
        validate_numeric_literals(pair.into_inner())?;
    }
    Ok(())
}

#[cfg(test)]
mod literal_tests {
    use super::compile;

    #[test]
    fn rejects_malformed_integer_separators() {
        for code in ["1__0", "1_", "0x_2A_", "0b1__0"] {
            assert!(compile(code).is_err(), "{code} should be rejected");
        }
    }

    #[test]
    fn rejects_integer_overflow_without_panicking() {
        assert!(compile("0x10000000000000000").is_err());
        assert!(compile("9223372036854775808").is_err());
    }

    #[test]
    fn accepts_scientific_float_literals() {
        for code in ["1e3", "1.2e-4", ".5e+2", "1_000.5_0e-2"] {
            assert!(compile(code).is_ok(), "{code} should be accepted");
        }
    }

    #[test]
    fn rejects_malformed_or_overflowing_float_literals() {
        for code in ["1e", "1e+", "1e_2", "1e9999"] {
            assert!(compile(code).is_err(), "{code} should be rejected");
        }
    }
}

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
#[deprecated(note = "Use `compile()` and `Environment` instead")]
#[derive(Default)]
pub struct Parser<'a> {
    env: Environment<'a>,
}

#[allow(deprecated)]
impl Debug for Parser<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("ExprParser").finish()
    }
}

#[allow(deprecated)]
impl<'a> Parser<'a> {
    /// Create a new parser with the default environment
    pub fn new() -> Self {
        Parser {
            env: Environment::new(),
        }
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
    ///       if let Value::Integer(n) = arg {
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
        self.env.add_function(name, Box::new(f));
    }

    /// Parse an expr program to be run later
    pub fn compile(&self, code: &str) -> Result<Program> {
        compile(code)
    }

    /// Run a compiled expr program
    pub fn run(&self, program: &Program, ctx: &dyn ContextProvider) -> Result<Value> {
        self.env.run(program, ctx)
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
    pub fn eval(&self, code: &str, ctx: &dyn ContextProvider) -> Result<Value> {
        self.env.eval(code, ctx)
    }

    pub fn eval_expr(&self, ctx: &dyn ContextProvider, node: &Node) -> Result<Value> {
        self.env.eval_expr(ctx, node)
    }
}
