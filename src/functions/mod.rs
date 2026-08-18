pub mod array;
pub mod bitwise;
pub mod convert;
pub mod json;
pub mod string;

use crate::Result;

use crate::ast::program::Program;
use crate::{bail, Environment, EvalContext, Value};

pub type Function<'a> = Box<dyn Fn(ExprCall) -> Result<Value> + 'a + Sync + Send>;

pub struct ExprCall<'a, 'b, 'c> {
    pub ident: String,
    pub args: Vec<Value>,
    pub predicate: Option<&'a Program>,
    pub ctx: &'a EvalContext<'b>,
    pub env: &'a Environment<'c>,
}

impl Environment<'_> {
    pub fn eval_func(&self, ctx: &EvalContext, ident: &str, args: Vec<Value>, predicate: Option<&Program>) -> Result<Value> {
        let call = ExprCall {
            ident: ident.to_string(),
            args,
            predicate,
            ctx,
            env: self,
        };
        if let Some(f) = self.functions.get(&call.ident) {
            f(call)
        } else {
            bail!("Unknown function: {}", call.ident)
        }
    }
}
