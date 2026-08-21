use crate::Rule;
use std::sync::LazyLock;
use pest::pratt_parser::PrattParser;

pub(crate) static PRATT_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    use pest::pratt_parser::{Assoc::*, Op};
    use Rule::*;

    PrattParser::new()
        .op(Op::postfix(ternary))
        .op(Op::postfix(pipe))
        .op(Op::infix(or_op, Left))
        .op(Op::infix(and_op, Left))
        .op(Op::infix(equal_op, Left)
            | Op::infix(comparison_op, Left)
            | Op::infix(not_in_op, Left)
            | Op::infix(string_op, Left))
        .op(Op::infix(range_op, Left))
        .op(Op::infix(addition_op, Left))
        .op(Op::prefix(negation_op))
        .op(Op::infix(multiplication_op, Left))
        .op(Op::prefix(sign_op))
        .op(Op::infix(exponent_op, Right))
        .op(Op::postfix(default_op))
        .op(Op::postfix(method_call)
            | Op::postfix(membership_op)
            | Op::postfix(index_op)
            | Op::postfix(opt_membership_op)
            | Op::postfix(opt_index_op)
            | Op::postfix(range_start_op)
            | Op::postfix(range_end_op))
});
