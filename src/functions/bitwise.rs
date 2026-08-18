use crate::{bail, Environment, Value};

fn one_integer(name: &str, mut args: Vec<Value>) -> crate::Result<i64> {
    if args.len() != 1 {
        bail!(
            "invalid number of arguments for {name} (expected 1, got {})",
            args.len()
        );
    }
    match args.pop().expect("length checked") {
        Value::Integer(value) => Ok(value),
        _ => bail!("invalid argument for {name} (expected integer)"),
    }
}

fn two_integers(name: &str, args: Vec<Value>) -> crate::Result<(i64, i64)> {
    if args.len() != 2 {
        bail!(
            "invalid number of arguments for {name} (expected 2, got {})",
            args.len()
        );
    }
    let mut args = args.into_iter();
    match (
        args.next().expect("length checked"),
        args.next().expect("length checked"),
    ) {
        (Value::Integer(left), Value::Integer(right)) => Ok((left, right)),
        _ => bail!("invalid arguments for {name} (expected integers)"),
    }
}

fn shift_count(name: &str, count: i64) -> crate::Result<u32> {
    if count < 0 {
        bail!("invalid operation: negative shift count {count} (type integer)");
    }
    u32::try_from(count).map_err(|_| format!("invalid shift count for {name}: {count}").into())
}

/// Add expr's built-in bitwise functions.
pub fn add_bitwise_functions(env: &mut Environment) {
    env.add_function("bitand", |call| {
        let (left, right) = two_integers("bitand", call.args)?;
        Ok(Value::Integer(left & right))
    });
    env.add_function("bitor", |call| {
        let (left, right) = two_integers("bitor", call.args)?;
        Ok(Value::Integer(left | right))
    });
    env.add_function("bitxor", |call| {
        let (left, right) = two_integers("bitxor", call.args)?;
        Ok(Value::Integer(left ^ right))
    });
    env.add_function("bitnand", |call| {
        let (left, right) = two_integers("bitnand", call.args)?;
        Ok(Value::Integer(left & !right))
    });
    env.add_function("bitnot", |call| {
        Ok(Value::Integer(!one_integer("bitnot", call.args)?))
    });
    env.add_function("bitshl", |call| {
        let (value, count) = two_integers("bitshl", call.args)?;
        let count = shift_count("bitshl", count)?;
        Ok(Value::Integer(value.checked_shl(count).unwrap_or(0)))
    });
    env.add_function("bitshr", |call| {
        let (value, count) = two_integers("bitshr", call.args)?;
        let count = shift_count("bitshr", count)?;
        let shifted = value
            .checked_shr(count)
            .unwrap_or(if value < 0 { -1 } else { 0 });
        Ok(Value::Integer(shifted))
    });
    env.add_function("bitushr", |call| {
        let (value, count) = two_integers("bitushr", call.args)?;
        let count = shift_count("bitushr", count)?;
        Ok(Value::Integer(
            (value as u64).checked_shr(count).unwrap_or(0) as i64,
        ))
    });
}

#[cfg(test)]
mod tests {
    use crate::{eval, Context, Value};

    #[test]
    fn bitwise_builtins_match_expr() {
        let context = Context::default();
        let cases = [
            ("bitnot(156)", -157),
            ("bitand(bitnot(156), 255)", 99),
            ("bitor(987, -123)", -33),
            ("bitxor(15, 32)", 47),
            ("bitshl(39, 3)", 312),
            ("bitshr(5, 1)", 2),
            ("bitushr(-5, 2)", 4_611_686_018_427_387_902),
            ("bitnand(35, 9)", 34),
            ("bitshl(1, 64)", 0),
            ("bitshr(-5, 64)", -1),
            ("bitushr(-5, 64)", 0),
        ];

        for (code, expected) in cases {
            assert_eq!(eval(code, &context).unwrap(), Value::Integer(expected));
        }
    }

    #[test]
    fn bitwise_builtins_reject_invalid_arguments() {
        let context = Context::default();
        assert!(eval("bitnot()", &context).is_err());
        assert!(eval("bitand(1)", &context).is_err());
        assert!(eval("bitand(1, 2.0)", &context).is_err());
        assert!(eval("bitshl(1, -1)", &context).is_err());
    }
}
