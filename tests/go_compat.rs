use expr::{eval, Context, Value as ExprValue};
use base64::Engine;
use base64::engine::general_purpose::STANDARD;
use chrono::SecondsFormat;
use serde_json::{Map, Number, Value as JsonValue};

fn json_value(value: ExprValue) -> JsonValue {
    match value {
        ExprValue::Nil => JsonValue::Null,
        ExprValue::Bool(value) => JsonValue::Bool(value),
        ExprValue::Integer(value) => JsonValue::Number(value.into()),
        ExprValue::Float(value) => Number::from_f64(value)
            .map(JsonValue::Number)
            .unwrap_or(JsonValue::Null),
        ExprValue::String(value) => JsonValue::String(value),
        ExprValue::Bytes(value) => JsonValue::String(STANDARD.encode(value)),
        ExprValue::DateTime(value) => JsonValue::String(go_rfc3339(&value)),
        ExprValue::Duration(value) => JsonValue::Number(value.into()),
        ExprValue::Timezone(_) => JsonValue::Object(Default::default()),
        ExprValue::Month(value) | ExprValue::Weekday(value) => {
            JsonValue::Number(value.into())
        }
        ExprValue::Array(values) => JsonValue::Array(values.into_iter().map(json_value).collect()),
        ExprValue::Map(values) => JsonValue::Object(
            values
                .into_iter()
                .map(|(key, value)| (key, json_value(value)))
                .collect::<Map<_, _>>(),
        ),
        ExprValue::KeyedMap(values) => JsonValue::Array(
            values
                .into_iter()
                .map(|(key, value)| JsonValue::Array(vec![json_value(key), json_value(value)]))
                .collect(),
        ),
    }
}

fn go_rfc3339(value: &expr::DateTimeValue) -> String {
    let value = value.to_rfc3339_opts(SecondsFormat::Nanos, true);
    let Some(decimal) = value.find('.') else {
        return value;
    };
    let zone = value[decimal..]
        .find(['Z', '+', '-'])
        .map(|index| decimal + index)
        .unwrap_or(value.len());
    let fraction = value[decimal + 1..zone].trim_end_matches('0');
    if fraction.is_empty() {
        format!("{}{}", &value[..decimal], &value[zone..])
    } else {
        format!("{}.{}{}", &value[..decimal], fraction, &value[zone..])
    }
}

fn json_values_equal(left: &JsonValue, right: &JsonValue) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (JsonValue::Number(left), JsonValue::Number(right)) => {
            (left.is_f64() || right.is_f64()) && left.as_f64() == right.as_f64()
        }
        (JsonValue::Array(left), JsonValue::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| json_values_equal(left, right))
        }
        (JsonValue::Object(left), JsonValue::Object(right)) => {
            left.len() == right.len()
                && left.iter().all(|(key, left)| {
                    right
                        .get(key)
                        .is_some_and(|right| json_values_equal(left, right))
                })
        }
        _ => false,
    }
}

#[test]
fn json_comparison_preserves_integer_precision() {
    let left = serde_json::from_str::<JsonValue>("9007199254740992").unwrap();
    let right = serde_json::from_str::<JsonValue>("9007199254740993").unwrap();
    assert!(!json_values_equal(&left, &right));

    let float = serde_json::from_str::<JsonValue>("5.0").unwrap();
    let integer = serde_json::from_str::<JsonValue>("5").unwrap();
    assert!(json_values_equal(&float, &integer));
}

#[test]
fn rejects_go_expr_v1_17_8_error_corpus() {
    let context = Context::default();
    for (index, expression) in include_str!("../compat/errors.tsv").lines().enumerate() {
        if expression.is_empty() || expression.starts_with('#') {
            continue;
        }
        assert!(
            eval(expression, &context).is_err(),
            "compat/errors.tsv:{}: expected {expression:?} to fail",
            index + 1
        );
    }
}

#[test]
fn matches_go_expr_v1_17_8_corpus() {
    let context = Context::default();
    for (index, line) in include_str!("../compat/cases.tsv").lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (expression, expected) = line
            .split_once('\t')
            .unwrap_or_else(|| panic!("compat/cases.tsv:{}: invalid case", index + 1));
        let actual = eval(expression, &context)
            .unwrap_or_else(|error| panic!("compat/cases.tsv:{}: {error}", index + 1));
        let expected = serde_json::from_str::<JsonValue>(expected)
            .unwrap_or_else(|error| panic!("compat/cases.tsv:{}: {error}", index + 1));
        let actual = json_value(actual);
        assert!(
            json_values_equal(&actual, &expected),
            "compat/cases.tsv:{}: {expression}: got {actual}, want {expected}",
            index + 1,
        );
    }
}
