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

/// Register builtins that report the feature they need instead of not existing.
///
/// A builtin whose feature is off is still a builtin the language has: `Unknown function:
/// fromJSON` sends an author hunting for a typo, when what is missing is a Cargo feature and
/// only the person who chose the features can fix it. Same contract as the `matches` operator
/// and method dispatch, which report their own features.
#[cfg(not(all(feature = "base64", feature = "json", feature = "temporal")))]
pub(crate) fn add_disabled_functions(
    env: &mut Environment,
    feature: &'static str,
    names: &[&'static str],
) {
    for name in names {
        env.add_function(name, move |call| {
            bail!(
                "{}() requires expr-lang's `{feature}` feature",
                call.ident
            )
        });
    }
}

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
