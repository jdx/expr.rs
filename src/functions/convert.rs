use crate::{Environment, Value, bail};

fn one_arg(name: &str, mut args: Vec<Value>) -> crate::Result<Value> {
    if args.len() != 1 {
        bail!(
            "invalid number of arguments for {name} (expected 1, got {})",
            args.len()
        );
    }
    Ok(args.pop().expect("length checked"))
}

fn go_float_string(value: f64) -> String {
    if value.is_nan() {
        return "NaN".to_string();
    }
    if value == f64::INFINITY {
        return "+Inf".to_string();
    }
    if value == f64::NEG_INFINITY {
        return "-Inf".to_string();
    }

    let rendered = value.to_string();
    let (sign, unsigned) = rendered
        .strip_prefix('-')
        .map_or(("", rendered.as_str()), |value| ("-", value));
    let (mantissa, explicit_exponent) = unsigned
        .split_once(['e', 'E'])
        .map_or((unsigned, 0), |(mantissa, exponent)| {
            (mantissa, exponent.parse::<i32>().expect("valid exponent"))
        });
    let decimal_point = mantissa.find('.').unwrap_or(mantissa.len()) as i32;
    let mut digits = mantissa.replace('.', "");
    let leading_zeroes = digits.len() - digits.trim_start_matches('0').len();
    digits.drain(..leading_zeroes);

    if digits.is_empty() {
        return format!("{sign}0");
    }

    let exponent = decimal_point - leading_zeroes as i32 - 1 + explicit_exponent;
    while digits.ends_with('0') {
        digits.pop();
    }

    if !(-4..6).contains(&exponent) {
        let mut output = format!("{sign}{}", &digits[..1]);
        if digits.len() > 1 {
            output.push('.');
            output.push_str(&digits[1..]);
        }
        output.push('e');
        output.push(if exponent < 0 { '-' } else { '+' });
        output.push_str(&format!("{:02}", exponent.abs()));
        return output;
    }

    if exponent < 0 {
        format!("{sign}0.{}{digits}", "0".repeat((-exponent - 1) as usize))
    } else {
        let decimal_point = exponent as usize + 1;
        if decimal_point >= digits.len() {
            format!("{sign}{digits}{}", "0".repeat(decimal_point - digits.len()))
        } else {
            format!(
                "{sign}{}.{}",
                &digits[..decimal_point],
                &digits[decimal_point..]
            )
        }
    }
}

fn expr_string(value: &Value) -> String {
    match value {
        Value::Integer(value) => value.to_string(),
        Value::Float(value) => go_float_string(*value),
        Value::Bool(value) => value.to_string(),
        Value::Nil => "<nil>".to_string(),
        Value::String(value) => value.clone(),
        Value::Bytes(values) => format!(
            "[{}]",
            values.iter().map(u8::to_string).collect::<Vec<_>>().join(" ")
        ),
        Value::DateTime(value) => value.to_rfc3339(),
        Value::Duration(value) => crate::functions::temporal::format_duration(*value),
        Value::Timezone(value) => value.to_string(),
        Value::Month(value) => crate::functions::temporal::month_name(*value).to_string(),
        Value::Weekday(value) => crate::functions::temporal::weekday_name(*value).to_string(),
        Value::Array(values) => format!(
            "[{}]",
            values.iter().map(expr_string).collect::<Vec<_>>().join(" ")
        ),
        Value::Map(values) => format!(
            "map[{}]",
            {
                let mut values = values.iter().collect::<Vec<_>>();
                values.sort_unstable_by_key(|(key, _)| key.as_str());
                values
            }
            .into_iter()
            .map(|(key, value)| format!("{key}:{}", expr_string(value)))
            .collect::<Vec<_>>()
            .join(" ")
        ),
    }
}

/// Add expr's built-in conversion functions.
pub fn add_conversion_functions(env: &mut Environment) {
    env.add_function("int", |call| match one_arg("int", call.args)? {
        Value::Integer(value) => Ok(value.into()),
        Value::Float(value) => Ok((value as i64).into()),
        Value::String(value) => value
            .parse::<i64>()
            .map(Value::Integer)
            .map_err(|_| format!("invalid operation: int({value})").into()),
        value => bail!("invalid operation: int({})", expr_string(&value)),
    });

    env.add_function("float", |call| match one_arg("float", call.args)? {
        Value::Integer(value) => Ok((value as f64).into()),
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
    use super::expr_string;
    use crate::{Context, Value, eval};

    #[test]
    fn conversion_builtins_match_expr() {
        let context = Context::default();
        let cases = [
            ("int(5.5)", Value::Integer(5)),
            ("int(5)", Value::Integer(5)),
            (r#"int("5")"#, Value::Integer(5)),
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

    #[test]
    fn string_matches_go_float_formatting() {
        let cases = [
            (f64::NAN, "NaN"),
            (f64::INFINITY, "+Inf"),
            (f64::NEG_INFINITY, "-Inf"),
            (1e-4, "0.0001"),
            (1e-5, "1e-05"),
            (1e6, "1e+06"),
            (1e20, "1e+20"),
        ];

        for (value, expected) in cases {
            assert_eq!(expr_string(&Value::Float(value)), expected);
        }
    }

    #[test]
    fn string_sorts_map_keys_like_go() {
        let value = [("c", 3), ("b", 2), ("a", 1)].into_iter().collect();
        assert_eq!(expr_string(&value), "map[a:1 b:2 c:3]");
    }
}
