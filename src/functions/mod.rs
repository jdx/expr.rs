pub mod array;
pub mod bitwise;
pub mod collection;
pub mod convert;
pub mod json;
pub mod misc;
pub mod number;
pub mod string;
#[cfg(feature = "temporal")]
pub mod temporal;

use crate::Result;

use crate::ast::program::Program;
use crate::{bail, ContextProvider, Environment, Value};

pub type Function<'a> = Box<dyn Fn(ExprCall) -> Result<Value> + 'a + Sync + Send>;

pub struct ExprCall<'a, 'b> {
    pub ident: String,
    pub args: Vec<Value>,
    pub predicate: Option<&'a Program>,
    pub ctx: &'a dyn ContextProvider,
    pub env: &'a Environment<'b>,
}

impl Environment<'_> {
    pub fn eval_func(
        &self,
        ctx: &dyn ContextProvider,
        ident: &str,
        args: Vec<Value>,
        predicate: Option<&Program>,
    ) -> Result<Value> {
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
