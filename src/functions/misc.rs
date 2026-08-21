use crate::{Environment, Value, bail};
#[cfg(feature = "base64")]
use crate::Error;
#[cfg(feature = "base64")]
use base64::Engine;
#[cfg(feature = "base64")]
use base64::engine::general_purpose::STANDARD;

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
            #[cfg(feature = "temporal")]
            Value::DateTime(_) => "time.Time",
            #[cfg(feature = "temporal")]
            Value::Duration(_) => "time.Duration",
            #[cfg(feature = "temporal")]
            Value::Timezone(_) => "time.Location",
            #[cfg(feature = "temporal")]
            Value::Month(_) => "time.Month",
            #[cfg(feature = "temporal")]
            Value::Weekday(_) => "time.Weekday",
            Value::Array(_) => "array",
            Value::Map(_) => "map",
            Value::KeyedMap(_) => "map",
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
            (Value::KeyedMap(values), key) => Ok(values
                .iter()
                .find(|(candidate, _)| crate::ast::operator::map_keys_equal(candidate, key))
                .map(|(_, value)| value.clone())
                .unwrap_or_default()),
            _ => bail!("get() takes an array or bytes and integer, or a map and key"),
        }
    });

    #[cfg(not(feature = "base64"))]
    super::add_disabled_functions(env, "base64", &["toBase64", "fromBase64"]);
    #[cfg(feature = "base64")]
    env.add_function("toBase64", |call| match one_argument("toBase64", call.args)? {
        Value::String(value) => Ok(Value::from(STANDARD.encode(value))),
        _ => bail!("toBase64() takes a string as the argument"),
    });
    #[cfg(feature = "base64")]
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
        Value::KeyedMap(values) => Ok(Value::Array(
            values
                .into_iter()
                .map(|(key, value)| Value::Array(vec![key, value]))
                .collect(),
        )),
        _ => bail!("toPairs() takes a map as the argument"),
    });
    env.add_function("fromPairs", |call| match one_argument("fromPairs", call.args)? {
        Value::Array(pairs) => {
            let mut values = Vec::new();
            for pair in pairs {
                match pair {
                    Value::Array(pair) if pair.len() == 2 => {
                        let mut pair = pair.into_iter();
                        let key = pair.next().expect("length checked");
                        let value = pair.next().expect("length checked");
                        if !crate::ast::operator::is_comparable_map_key(&key) {
                            bail!("fromPairs() map key is not comparable");
                        }
                        if let Some((_, existing)) = values.iter_mut().find(|(candidate, _)| {
                            crate::ast::operator::map_keys_equal(candidate, &key)
                        }) {
                            *existing = value;
                        } else {
                            values.push((key, value));
                        }
                    }
                    _ => bail!("fromPairs() expects an array of two-element arrays"),
                }
            }
            Ok(Value::KeyedMap(values))
        }
        _ => bail!("fromPairs() takes an array as the argument"),
    });
}
