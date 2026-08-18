use crate::{bail, Environment, Value};

fn one_arg(name: &str, mut args: Vec<Value>) -> crate::Result<Value> {
    if args.len() != 1 {
        bail!(
            "invalid number of arguments for {name} (expected 1, got {})",
            args.len()
        );
    }
    Ok(args.pop().expect("length checked"))
}

fn expr_string(value: &Value) -> String {
    match value {
        Value::Number(value) => value.to_string(),
        Value::Float(value) => value.to_string(),
        Value::Bool(value) => value.to_string(),
        Value::Nil => "<nil>".to_string(),
        Value::String(value) => value.clone(),
        Value::Array(values) => format!(
            "[{}]",
            values.iter().map(expr_string).collect::<Vec<_>>().join(" ")
        ),
        Value::Map(values) => format!(
            "map[{}]",
            values
                .iter()
                .map(|(key, value)| format!("{key}:{}", expr_string(value)))
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

/// Add expr's built-in conversion functions.
pub fn add_conversion_functions(env: &mut Environment) {
    env.add_function("int", |call| match one_arg("int", call.args)? {
        Value::Number(value) => Ok(value.into()),
        Value::Float(value) => Ok((value as i64).into()),
        Value::String(value) => value
            .parse::<i64>()
            .map(Value::Number)
            .map_err(|_| format!("invalid operation: int({value})").into()),
        value => bail!("invalid operation: int({})", expr_string(&value)),
    });

    env.add_function("float", |call| match one_arg("float", call.args)? {
        Value::Number(value) => Ok((value as f64).into()),
        Value::Float(value) => Ok(value.into()),
        Value::String(value) => value
            .parse::<f64>()
            .map(Value::Float)
            .map_err(|_| format!("invalid operation: float({value})").into()),
        value => bail!("invalid operation: float({})", expr_string(&value)),
    });

    env.add_function("string", |call| {
        let value = one_arg("string", call.args)?;
        Ok(expr_string(&value).into())
    });
}

#[cfg(test)]
mod tests {
    use crate::{eval, Context, Value};

    #[test]
    fn conversion_builtins_match_expr() {
        let context = Context::default();
        let cases = [
            ("int(5.5)", Value::Number(5)),
            ("int(5)", Value::Number(5)),
            (r#"int("5")"#, Value::Number(5)),
            ("float(5)", Value::Float(5.0)),
            ("float(5.5)", Value::Float(5.5)),
            (r#"float("5.5")"#, Value::Float(5.5)),
            ("string(5)", Value::String("5".to_string())),
            ("string(5.5)", Value::String("5.5".to_string())),
            (
                r#"string("already text")"#,
                Value::String("already text".to_string()),
            ),
        ];

        for (code, expected) in cases {
            assert_eq!(eval(code, &context).unwrap(), expected, "{code}");
        }
    }

    #[test]
    fn conversions_report_invalid_input() {
        let context = Context::default();
        assert!(eval("int()", &context).is_err());
        assert!(eval("int(1, 2)", &context).is_err());
        assert!(eval(r#"int("five")"#, &context).is_err());
        assert!(eval(r#"float("five")"#, &context).is_err());
    }
}
