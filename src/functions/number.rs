use crate::{Environment, Value, bail};

fn one_number(name: &str, mut args: Vec<Value>) -> crate::Result<Value> {
    if args.len() != 1 {
        bail!("{name}() takes exactly one argument");
    }
    match args.pop().expect("length checked") {
        value @ (Value::Integer(_) | Value::Float(_)) => Ok(value),
        _ => bail!("{name}() takes a number as the argument"),
    }
}

fn two_numbers(name: &str, args: Vec<Value>) -> crate::Result<(Value, Value)> {
    if args.len() != 2 {
        bail!("{name}() takes exactly two arguments");
    }
    let mut args = args.into_iter();
    let left = args.next().expect("length checked");
    let right = args.next().expect("length checked");
    if !matches!(left, Value::Integer(_) | Value::Float(_))
        || !matches!(right, Value::Integer(_) | Value::Float(_))
    {
        bail!("{name}() takes numbers as arguments");
    }
    Ok((left, right))
}

fn extrema(name: &str, args: Vec<Value>, maximum: bool) -> crate::Result<Value> {
    let (left, right) = two_numbers(name, args)?;
    Ok(match (left, right) {
        (Value::Integer(left), Value::Integer(right)) => {
            Value::Integer(if maximum { left.max(right) } else { left.min(right) })
        }
        (Value::Integer(left), Value::Float(right)) => {
            let left = left as f64;
            Value::Float(if maximum { left.max(right) } else { left.min(right) })
        }
        (Value::Float(left), Value::Integer(right)) => {
            let right = right as f64;
            Value::Float(if maximum { left.max(right) } else { left.min(right) })
        }
        (Value::Float(left), Value::Float(right)) => {
            Value::Float(if maximum { left.max(right) } else { left.min(right) })
        }
        _ => unreachable!("validated numeric arguments"),
    })
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
    env.add_function("ceil", |call| match one_number("ceil", call.args)? {
        Value::Float(value) => Ok(Value::Float(value.ceil())),
        _ => bail!("ceil() takes a float as the argument"),
    });
    env.add_function("floor", |call| match one_number("floor", call.args)? {
        Value::Float(value) => Ok(Value::Float(value.floor())),
        _ => bail!("floor() takes a float as the argument"),
    });
    env.add_function("round", |call| match one_number("round", call.args)? {
        Value::Float(value) => Ok(Value::Float(value.round())),
        _ => bail!("round() takes a float as the argument"),
    });
}
