use crate::Rule;
use once_cell::sync::Lazy;
use pest::pratt_parser::PrattParser;

pub(crate) static PRATT_PARSER: Lazy<PrattParser<Rule>> = Lazy::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;

    PrattParser::new()
        .op(Op::postfix(membership_op)
            | Op::postfix(ternary)
            | Op::postfix(index_op)
            | Op::postfix(default_op)
            | Op::postfix(opt_membership_op)
            | Op::postfix(opt_index_op)
            | Op::postfix(range_start_op)
            | Op::postfix(range_end_op)
            | Op::postfix(pipe))
        .op(Op::prefix(unary_op))
        .op(Op::infix(string_op, Left))
        .op(Op::infix(or_op, Left))
        .op(Op::infix(and_op, Left))
        .op(Op::infix(equal_op, Left))
        .op(Op::infix(comparison_op, Left))
        .op(Op::infix(addition_op, Left))
        .op(Op::infix(factor_op, Left))
});
