pub mod string;
pub mod array;

use crate::Result;

use crate::ast::program::Program;
use crate::{bail, Context, Parser, Value};

pub type Function<'a> = Box<dyn Fn(ExprCall) -> Result<Value> + 'a + Sync + Send>;

pub struct ExprCall<'a, 'b> {
    pub ident: String,
    pub args: Vec<Value>,
    pub predicate: Option<Program>,
    pub ctx: &'a Context,
    pub parser: &'a Parser<'b>,
}

impl Parser<'_> {
    pub fn exec_func(&self, ctx: &Context, ident: String, args: Vec<Value>, predicate: Option<Program>) -> Result<Value> {
        let call = ExprCall {
            ident,
            args,
            predicate,
            ctx,
            parser: self,
        };
        if let Some(f) = self.functions.get(&call.ident) {
            f(call)
        } else {
            bail!("Unknown function: {}", call.ident)
        }
    }
}
