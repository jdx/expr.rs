#[cfg(feature = "json")]
use serde_json;

use crate::{bail, Environment, Value};
#[cfg(feature = "json")]
use crate::Result;
#[cfg(feature = "json")]
use base64::Engine;
#[cfg(feature = "json")]
use base64::engine::general_purpose::STANDARD;

/// Convert a serde_json::Value to an expr::Value
#[cfg(feature = "json")]
fn json_to_value(json: serde_json::Value) -> Value {
    match json {
        serde_json::Value::Null => Value::Nil,
        serde_json::Value::Bool(b) => Value::Bool(b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Value::Integer(i)
            } else if let Some(f) = n.as_f64() {
                Value::Float(f)
            } else {
                Value::Nil
            }
        }
        serde_json::Value::String(s) => Value::String(s),
        serde_json::Value::Array(arr) => {
            Value::Array(arr.into_iter().map(json_to_value).collect())
        }
        serde_json::Value::Object(obj) => {
            Value::Map(obj.into_iter().map(|(k, v)| (k, json_to_value(v))).collect())
        }
    }
}

/// Convert an expr::Value to a serde_json::Value
#[cfg(feature = "json")]
fn value_to_json(value: &Value) -> Result<serde_json::Value> {
    Ok(match value {
        Value::Nil => serde_json::Value::Null,
        Value::Bool(b) => serde_json::Value::Bool(*b),
        Value::Integer(n) => serde_json::Value::Number((*n).into()),
        Value::Float(f) => {
            serde_json::Number::from_f64(*f)
                .map(serde_json::Value::Number)
                .unwrap_or(serde_json::Value::Null)
        }
        Value::String(s) => serde_json::Value::String(s.clone()),
        Value::Bytes(bytes) => serde_json::Value::String(STANDARD.encode(bytes)),
        #[cfg(feature = "temporal")]
        Value::DateTime(value) => serde_json::Value::String(
            crate::functions::temporal::date_to_rfc3339(value),
        ),
        #[cfg(feature = "temporal")]
        Value::Duration(value) => serde_json::Value::Number((*value).into()),
        #[cfg(feature = "temporal")]
        Value::Timezone(_) => serde_json::Value::Object(Default::default()),
        #[cfg(feature = "temporal")]
        Value::Month(value) | Value::Weekday(value) => {
            serde_json::Value::Number((*value).into())
        }
        Value::Array(arr) => serde_json::Value::Array(
            arr.iter().map(value_to_json).collect::<Result<Vec<_>>>()?
        ),
        Value::Map(m) => {
            serde_json::Value::Object(
                m.iter()
                    .map(|(k, v)| Ok((k.clone(), value_to_json(v)?)))
                    .collect::<Result<_>>()?
            )
        }
        Value::KeyedMap(_) => bail!("toJSON() does not support arbitrary-key maps"),
    })
}

pub fn add_json_functions(env: &mut Environment) {
    // `keys`, `values` and `len` are in this module too and are not JSON: they read a map or
    // an array and need no crate to do it, so only the codec follows the feature.
    #[cfg(not(feature = "json"))]
    super::add_disabled_functions(env, "json", &["fromJSON", "toJSON"]);

    // fromJSON(string) -> Value
    // Parses a JSON string and returns the corresponding Value
    #[cfg(feature = "json")]
    env.add_function("fromJSON", |c| {
        if c.args.len() != 1 {
            bail!("fromJSON() takes exactly one argument");
        }
        if let Value::String(s) = &c.args[0] {
            match serde_json::from_str::<serde_json::Value>(s) {
                Ok(json) => Ok(json_to_value(json)),
                Err(e) => bail!("fromJSON() failed to parse JSON: {}", e),
            }
        } else {
            bail!("fromJSON() takes a string as the argument");
        }
    });

    // toJSON(value) -> String
    // Serializes a value to a JSON string
    #[cfg(feature = "json")]
    env.add_function("toJSON", |c| {
        if c.args.len() != 1 {
            bail!("toJSON() takes exactly one argument");
        }
        let json = value_to_json(&c.args[0])?;
        match serde_json::to_string(&json) {
            Ok(s) => Ok(Value::String(s)),
            Err(e) => bail!("toJSON() failed to serialize: {}", e),
        }
    });

    // keys(map) -> Array of keys
    // Returns an array of the keys in a map
    env.add_function("keys", |c| {
        if c.args.len() != 1 {
            bail!("keys() takes exactly one argument");
        }
        match &c.args[0] {
            Value::Map(m) => Ok(Value::Array(
                m.keys().map(|k| Value::String(k.clone())).collect()
            )),
            Value::KeyedMap(m) => Ok(Value::Array(
                m.iter().map(|(key, _)| key.clone()).collect()
            )),
            _ => bail!("keys() takes a map as the argument"),
        }
    });

    // values(map) -> Array of values
    // Returns an array of the values in a map
    env.add_function("values", |c| {
        if c.args.len() != 1 {
            bail!("values() takes exactly one argument");
        }
        match &c.args[0] {
            Value::Map(m) => Ok(Value::Array(m.values().cloned().collect())),
            Value::KeyedMap(m) => Ok(Value::Array(
                m.iter().map(|(_, value)| value.clone()).collect()
            )),
            _ => bail!("values() takes a map as the argument"),
        }
    });

    // len(array|string|map) -> Integer
    // Returns the length of an array, string, or map
    env.add_function("len", |c| {
        if c.args.len() != 1 {
            bail!("len() takes exactly one argument");
        }
        match &c.args[0] {
            Value::Array(a) => Ok(Value::Integer(a.len() as i64)),
            Value::String(s) => Ok(Value::Integer(s.chars().count() as i64)),
            Value::Bytes(bytes) => Ok(Value::Integer(bytes.len() as i64)),
            Value::Map(m) => Ok(Value::Integer(m.len() as i64)),
            Value::KeyedMap(m) => Ok(Value::Integer(m.len() as i64)),
            _ => bail!("len() takes an array, string, or map as the argument"),
        }
    });
}
