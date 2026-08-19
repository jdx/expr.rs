use crate::{Environment, Error, Value, bail};
use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use indexmap::IndexMap;

fn one_argument(name: &str, mut args: Vec<Value>) -> crate::Result<Value> {
    if args.len() != 1 {
        bail!("{name}() takes exactly one argument");
    }
    Ok(args.pop().expect("length checked"))
}

/// Add Go expr-compatible miscellaneous and collection conversion functions.
pub fn add_misc_functions(env: &mut Environment) {
    env.add_function("type", |call| {
        let name = match one_argument("type", call.args)? {
            Value::Nil => "nil",
            Value::Bool(_) => "bool",
            Value::Integer(_) => "int",
            Value::Float(_) => "float",
            Value::String(_) => "string",
            Value::Bytes(_) => "array",
            Value::DateTime(_) => "time.Time",
            Value::Duration(_) => "time.Duration",
            Value::Timezone(_) => "time.Location",
            Value::Month(_) => "time.Month",
            Value::Weekday(_) => "time.Weekday",
            Value::Array(_) => "array",
            Value::Map(_) => "map",
        };
        Ok(Value::from(name))
    });

    env.add_function("get", |call| {
        if call.args.len() != 2 {
            bail!("get() takes exactly two arguments");
        }
        match (&call.args[0], &call.args[1]) {
            (Value::Array(values), Value::Integer(index)) => {
                let index = if *index < 0 {
                    usize::try_from(index.unsigned_abs())
                        .ok()
                        .and_then(|offset| values.len().checked_sub(offset))
                } else {
                    usize::try_from(*index).ok()
                };
                Ok(index
                    .and_then(|index| values.get(index))
                    .cloned()
                    .unwrap_or_default())
            }
            (Value::Bytes(values), Value::Integer(index)) => {
                let index = if *index < 0 {
                    usize::try_from(index.unsigned_abs())
                        .ok()
                        .and_then(|offset| values.len().checked_sub(offset))
                } else {
                    usize::try_from(*index).ok()
                };
                Ok(index
                    .and_then(|index| values.get(index))
                    .map(|value| Value::Integer((*value).into()))
                    .unwrap_or_default())
            }
            (Value::Map(values), Value::String(key)) => {
                Ok(values.get(key).cloned().unwrap_or_default())
            }
            _ => bail!("get() takes an array or bytes and integer, or a map and string"),
        }
    });

    env.add_function("toBase64", |call| match one_argument("toBase64", call.args)? {
        Value::String(value) => Ok(Value::from(STANDARD.encode(value))),
        _ => bail!("toBase64() takes a string as the argument"),
    });
    env.add_function("fromBase64", |call| match one_argument("fromBase64", call.args)? {
        Value::String(value) => {
            let decoded = STANDARD
                .decode(value)
                .map_err(|error| Error::ExprError(format!("fromBase64() invalid input: {error}")))?;
            let decoded = String::from_utf8(decoded)
                .map_err(|error| {
                    Error::ExprError(format!("fromBase64() decoded non-UTF-8 data: {error}"))
                })?;
            Ok(Value::from(decoded))
        }
        _ => bail!("fromBase64() takes a string as the argument"),
    });

    env.add_function("toPairs", |call| match one_argument("toPairs", call.args)? {
        Value::Map(values) => Ok(Value::Array(
            values
                .into_iter()
                .map(|(key, value)| Value::Array(vec![Value::from(key), value]))
                .collect(),
        )),
        _ => bail!("toPairs() takes a map as the argument"),
    });
    env.add_function("fromPairs", |call| match one_argument("fromPairs", call.args)? {
        Value::Array(pairs) => {
            let mut values = IndexMap::new();
            for pair in pairs {
                match pair {
                    Value::Array(pair) if pair.len() == 2 => {
                        let mut pair = pair.into_iter();
                        let Value::String(key) = pair.next().expect("length checked") else {
                            bail!("fromPairs() pair keys must be strings");
                        };
                        values.insert(key, pair.next().expect("length checked"));
                    }
                    _ => bail!("fromPairs() expects an array of two-element arrays"),
                }
            }
            Ok(Value::Map(values))
        }
        _ => bail!("fromPairs() takes an array as the argument"),
    });
}
