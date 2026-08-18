use crate::{Environment, Value, bail};
use std::cmp::Ordering;

fn one_number(name: &str, mut args: Vec<Value>) -> crate::Result<Value> {
    if args.len() != 1 {
        bail!("{name}() takes exactly one argument");
    }
    match args.pop().expect("length checked") {
        value @ (Value::Integer(_) | Value::Float(_)) => Ok(value),
        _ => bail!("{name}() takes a number as the argument"),
    }
}

fn collect_numbers(name: &str, value: Value, numbers: &mut Vec<Value>) -> crate::Result<()> {
    match value {
        value @ (Value::Integer(_) | Value::Float(_)) => numbers.push(value),
        Value::Array(values) => {
            for value in values {
                collect_numbers(name, value, numbers)?;
            }
        }
        _ => bail!("invalid argument for {name} (expected number or array)"),
    }
    Ok(())
}

fn as_float(value: &Value) -> f64 {
    match value {
        Value::Integer(value) => *value as f64,
        Value::Float(value) => *value,
        _ => unreachable!("collected numeric value"),
    }
}

fn compare_integer_float(integer: i64, float: f64) -> Ordering {
    if float.is_nan() {
        return Ordering::Equal;
    }
    if float < i64::MIN as f64 {
        return Ordering::Greater;
    }
    if float >= 9_223_372_036_854_775_808.0 {
        return Ordering::Less;
    }

    let truncated = float as i64;
    match integer.cmp(&truncated) {
        Ordering::Equal if float.fract() > 0.0 => Ordering::Less,
        Ordering::Equal if float.fract() < 0.0 => Ordering::Greater,
        ordering => ordering,
    }
}

fn compare_numbers(left: &Value, right: &Value) -> Ordering {
    match (left, right) {
        (Value::Integer(left), Value::Integer(right)) => left.cmp(right),
        (Value::Integer(left), Value::Float(right)) => compare_integer_float(*left, *right),
        (Value::Float(left), Value::Integer(right)) => compare_integer_float(*right, *left).reverse(),
        (Value::Float(left), Value::Float(right)) => {
            left.partial_cmp(right).unwrap_or(Ordering::Equal)
        }
        _ => unreachable!("collected numeric value"),
    }
}

fn numbers(name: &str, args: Vec<Value>) -> crate::Result<Vec<Value>> {
    if args.is_empty() {
        bail!("not enough arguments to call {name}");
    }
    let mut numbers = Vec::new();
    for value in args {
        collect_numbers(name, value, &mut numbers)?;
    }
    Ok(numbers)
}

fn extrema(name: &str, args: Vec<Value>, maximum: bool) -> crate::Result<Value> {
    let mut numbers = numbers(name, args)?.into_iter();
    let Some(mut result) = numbers.next() else {
        return Ok(Value::Nil);
    };
    for value in numbers {
        let ordering = compare_numbers(&value, &result);
        let replace = if maximum {
            ordering.is_gt()
        } else {
            ordering.is_lt()
        };
        if replace {
            result = value;
        }
    }
    Ok(result)
}

/// Add Go expr-compatible numeric functions.
pub fn add_number_functions(env: &mut Environment) {
    env.add_function("max", |call| extrema("max", call.args, true));
    env.add_function("min", |call| extrema("min", call.args, false));
    env.add_function("abs", |call| match one_number("abs", call.args)? {
        Value::Integer(value) => value
            .checked_abs()
            .map(Value::Integer)
            .ok_or_else(|| "abs() integer overflow".to_string().into()),
        Value::Float(value) => Ok(Value::Float(value.abs())),
        _ => unreachable!("validated numeric argument"),
    });
    env.add_function("ceil", |call| {
        Ok(Value::Float(
            as_float(&one_number("ceil", call.args)?).ceil(),
        ))
    });
    env.add_function("floor", |call| {
        Ok(Value::Float(
            as_float(&one_number("floor", call.args)?).floor(),
        ))
    });
    env.add_function("round", |call| {
        Ok(Value::Float(
            as_float(&one_number("round", call.args)?).round(),
        ))
    });
    env.add_function("mean", |call| {
        let numbers = numbers("mean", call.args)?;
        if numbers.is_empty() {
            return Ok(Value::Float(0.0));
        }
        let mean = numbers.iter().map(as_float).sum::<f64>() / numbers.len() as f64;
        Ok(Value::Float(mean))
    });
    env.add_function("median", |call| {
        let mut numbers = numbers("median", call.args)?
            .iter()
            .map(as_float)
            .collect::<Vec<_>>();
        if numbers.is_empty() {
            return Ok(Value::Float(0.0));
        }
        numbers.sort_by(f64::total_cmp);
        let middle = numbers.len() / 2;
        let median = if numbers.len() % 2 == 0 {
            (numbers[middle - 1] + numbers[middle]) / 2.0
        } else {
            numbers[middle]
        };
        Ok(Value::Float(median))
    });
}

#[cfg(test)]
mod tests {
    use crate::{Context, Value, eval};

    #[test]
    fn extrema_preserve_mixed_numeric_order_above_f64_precision() {
        let context = Context::default();
        assert_eq!(
            eval("max(9007199254740992.0, 9007199254740993)", &context).unwrap(),
            Value::Integer(9_007_199_254_740_993)
        );
        assert_eq!(
            eval("min(9007199254740993, 9007199254740992.0)", &context).unwrap(),
            Value::Float(9_007_199_254_740_992.0)
        );
    }
}
