use crate::Rule;
use indexmap::IndexMap;
use log::trace;
use pest::iterators::{Pair, Pairs};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::{Add, Deref, Sub};

/// A time value together with the named timezone, when one is known.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct DateTimeValue {
    value: chrono::DateTime<chrono::FixedOffset>,
    #[cfg_attr(feature = "serde", serde(skip))]
    timezone: Option<chrono_tz::Tz>,
}

impl DateTimeValue {
    pub fn fixed(value: chrono::DateTime<chrono::FixedOffset>) -> Self {
        Self { value, timezone: None }
    }

    pub fn zoned(value: chrono::DateTime<chrono_tz::Tz>, timezone: chrono_tz::Tz) -> Self {
        Self { value: value.fixed_offset(), timezone: Some(timezone) }
    }

    pub(crate) fn with_timezone(&self, timezone: chrono_tz::Tz) -> Self {
        Self::zoned(self.value.with_timezone(&timezone), timezone)
    }

    pub fn checked_add_signed(mut self, duration: chrono::Duration) -> Option<Self> {
        self.value = self.value.checked_add_signed(duration)?;
        Some(self)
    }

    pub fn checked_sub_signed(mut self, duration: chrono::Duration) -> Option<Self> {
        self.value = self.value.checked_sub_signed(duration)?;
        Some(self)
    }

    pub(crate) fn zone_name(&self) -> String {
        if let Some(timezone) = self.timezone {
            self.value.with_timezone(&timezone).format("%Z").to_string()
        } else if self.value.offset().local_minus_utc() == 0 {
            "UTC".to_string()
        } else {
            self.value.format("%z").to_string()
        }
    }
}

impl From<chrono::DateTime<chrono::FixedOffset>> for DateTimeValue {
    fn from(value: chrono::DateTime<chrono::FixedOffset>) -> Self {
        Self::fixed(value)
    }
}

impl Deref for DateTimeValue {
    type Target = chrono::DateTime<chrono::FixedOffset>;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl PartialEq for DateTimeValue {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl PartialOrd for DateTimeValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl Add<chrono::Duration> for DateTimeValue {
    type Output = Self;

    fn add(mut self, duration: chrono::Duration) -> Self::Output {
        self.value += duration;
        self
    }
}

impl Sub<chrono::Duration> for DateTimeValue {
    type Output = Self;

    fn sub(mut self, duration: chrono::Duration) -> Self::Output {
        self.value -= duration;
        self
    }
}

impl Sub for DateTimeValue {
    type Output = chrono::Duration;

    fn sub(self, other: Self) -> Self::Output {
        self.value - other.value
    }
}

/// Represents a data value as input or output to an expr program
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(untagged))]
pub enum Value {
    Integer(i64),
    Bool(bool),
    Float(f64),
    #[default]
    Nil,
    String(String),
    DateTime(DateTimeValue),
    Duration(i64),
    Timezone(chrono_tz::Tz),
    Month(u32),
    Weekday(u32),
    Array(Vec<Value>),
    // Keep Bytes after Array so untagged serde treats JSON integer arrays as arrays.
    Bytes(Vec<u8>),
    Map(IndexMap<String, Value>),
}

impl Value {
    pub(crate) fn parse_integer(value: &str) -> std::result::Result<i64, std::num::ParseIntError> {
        let value = value.replace('_', "");
        let (digits, radix) = match value.as_bytes() {
            [b'0', b'x' | b'X', ..] => (&value[2..], 16),
            [b'0', b'o' | b'O', ..] => (&value[2..], 8),
            [b'0', b'b' | b'B', ..] => (&value[2..], 2),
            _ => (value.as_str(), 10),
        };
        i64::from_str_radix(digits, radix)
    }

    pub(crate) fn parse_float(value: &str) -> std::result::Result<f64, std::num::ParseFloatError> {
        value.replace('_', "").parse()
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_integer(&self) -> Option<i64> {
        match self {
            Value::Integer(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_float(&self) -> Option<f64> {
        match self {
            Value::Float(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_bytes(&self) -> Option<&[u8]> {
        match self {
            Value::Bytes(bytes) => Some(bytes),
            _ => None,
        }
    }

    pub fn as_datetime(&self) -> Option<&chrono::DateTime<chrono::FixedOffset>> {
        match self {
            Value::DateTime(value) => Some(&value.value),
            _ => None,
        }
    }

    pub fn as_duration(&self) -> Option<i64> {
        match self {
            Value::Duration(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }

    pub fn as_map(&self) -> Option<&IndexMap<String, Value>> {
        match self {
            Value::Map(m) => Some(m),
            _ => None,
        }
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }
}

impl<K, V> FromIterator<(K, V)> for Value
where
    K: Into<String>, 
    V: Into<Value>,
{
    fn from_iter<I>(iter: I) -> Self
    where I: IntoIterator<Item = (K, V)> {
        Value::Map(iter.into_iter().map(|(k, v)| (k.into(), v.into())).collect())
    }
}

impl AsRef<Value> for Value {
    fn as_ref(&self) -> &Value {
        self
    }
}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Integer(n)
    }
}

impl From<i32> for Value {
    fn from(n: i32) -> Self {
        Value::Integer(n as i64)
    }
}

impl From<usize> for Value {
    fn from(n: usize) -> Self {
        Value::Integer(n as i64)
    }
}

impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Value::Float(f)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
}

impl From<&String> for Value {
    fn from(s: &String) -> Self {
        s.to_string().into()
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        s.to_string().into()
    }
}

impl<V: Into<Value>> From<Vec<V>> for Value {
    fn from(a: Vec<V>) -> Self {
        Value::Array(a.into_iter().map(|v| v.into()).collect())
    }
}

impl From<IndexMap<String, Value>> for Value {
    fn from(m: IndexMap<String, Value>) -> Self {
        Value::Map(m)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Integer(n) => write!(f, "{n}"),
            Value::Float(n) => write!(f, "{n}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Nil => write!(f, "nil"),
            Value::String(s) => write!(
                f,
                r#""{}""#,
                s.replace("\\", "\\\\")
                    .replace("\n", "\\n")
                    .replace("\r", "\\r")
                    .replace("\t", "\\t")
                    .replace("\"", "\\\"")
            ),
            Value::Bytes(bytes) => write!(
                f,
                "[{}]",
                bytes
                    .iter()
                    .map(u8::to_string)
                    .collect::<Vec<String>>()
                    .join(" ")
            ),
            Value::DateTime(value) => write!(f, "{}", value.to_rfc3339()),
            Value::Duration(value) => write!(f, "{value}ns"),
            Value::Timezone(value) => write!(f, "{value}"),
            Value::Month(value) | Value::Weekday(value) => write!(f, "{value}"),
            Value::Array(a) => write!(
                f,
                "[{}]",
                a.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Value::Map(m) => write!(
                f,
                "{{{}}}",
                m.iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}

impl From<Pairs<'_, Rule>> for Value {
    fn from(mut pairs: Pairs<Rule>) -> Self {
        pairs.next().unwrap().into()
    }
}

impl From<Pair<'_, Rule>> for Value {
    fn from(pair: Pair<Rule>) -> Self {
        trace!("{:?} = {}", pair.as_rule(), pair.as_str());
        match pair.as_rule() {
            Rule::value => pair.into_inner().into(),
            Rule::nil => Value::Nil,
            Rule::bool => Value::Bool(pair.as_str().parse().unwrap()),
            Rule::int => {
                Value::Integer(Value::parse_integer(pair.as_str()).expect("literal validated"))
            }
            Rule::decimal => {
                Value::Float(Value::parse_float(pair.as_str()).expect("literal validated"))
            }
            Rule::bytes => Value::Bytes(parse_bytes_literal(pair.as_str())),
            Rule::string_multiline => pair.into_inner().as_str().into(),
            Rule::string => pair
                .into_inner()
                .as_str()
                .replace("\\\\", "\\")
                .replace("\\n", "\n")
                .replace("\\r", "\r")
                .replace("\\t", "\t")
                .replace("\\\"", "\"")
                .into(),
            // Rule::operation => {
            //     let mut pairs = pair.into_inner();
            //     let operator = pairs.next().unwrap().into();
            //     let left = Box::new(pairs.next().unwrap().into());
            //     let right = Box::new(pairs.next().unwrap().into());
            //     Node::Operation {
            //         operator,
            //         left,
            //         right,
            //     }
            // }
            rule => unreachable!("Unexpected rule: {rule:?} {}", pair.as_str()),
        }
    }
}

fn parse_bytes_literal(literal: &str) -> Vec<u8> {
    let mut chars = literal[2..literal.len() - 1].chars();
    let mut bytes = Vec::new();
    while let Some(character) = chars.next() {
        if character != '\\' {
            let mut encoded = [0; 4];
            bytes.extend_from_slice(character.encode_utf8(&mut encoded).as_bytes());
            continue;
        }

        let escape = chars.next().expect("byte escape validated by grammar");
        match escape {
            'a' => bytes.push(7),
            'b' => bytes.push(8),
            'f' => bytes.push(12),
            'n' => bytes.push(b'\n'),
            'r' => bytes.push(b'\r'),
            't' => bytes.push(b'\t'),
            'v' => bytes.push(11),
            '\\' | '\'' | '"' => bytes.push(escape as u8),
            'x' => {
                let digits = [
                    chars.next().expect("hex escape validated by grammar"),
                    chars.next().expect("hex escape validated by grammar"),
                ];
                bytes.push(
                    u8::from_str_radix(&digits.iter().collect::<String>(), 16)
                        .expect("hex escape validated by grammar"),
                );
            }
            digit @ '0'..='7' => {
                let digits = [
                    digit,
                    chars.next().expect("octal escape validated by grammar"),
                    chars.next().expect("octal escape validated by grammar"),
                ];
                bytes.push(
                    u8::from_str_radix(&digits.iter().collect::<String>(), 8)
                        .expect("octal escape validated by grammar"),
                );
            }
            _ => unreachable!("byte escape validated by grammar"),
        }
    }
    bytes
}
