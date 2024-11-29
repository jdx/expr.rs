use pest_derive::Parser as PestParser;

#[derive(PestParser)]
#[grammar = "expr.pest"]
pub(crate) struct ExprPest;
