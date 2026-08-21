use crate::ast::node::Node;
use crate::Value::{Array, Bool, Bytes, Float, Integer, KeyedMap, Map, String};
#[cfg(feature = "temporal")]
use crate::Value::{DateTime, Duration, Month, Weekday};
use crate::{bail, Result, Rule};
use crate::{ContextProvider, Environment, Value};
use log::trace;
use pest::iterators::Pair;
use std::fmt;

#[derive(Debug, Clone)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Pow,
    Equal,
    NotEqual,
    GreaterThan,
    GreaterThanOrEqual,
    LessThan,
    LessThanOrEqual,
    And,
    Or,
    In,
    NotIn,
    Contains,
    StartsWith,
    EndsWith,
    Matches,
}

impl Operator {
    /// How the operator is written in an error message.
    ///
    /// The word spelling for `and`/`or`, which is what an expression that reached an error
    /// most likely used: `&&` and `||` are the same operator by another name.
    fn as_str(&self) -> &'static str {
        match self {
            Operator::Add => "+",
            Operator::Subtract => "-",
            Operator::Multiply => "*",
            Operator::Divide => "/",
            Operator::Modulo => "%",
            Operator::Pow => "^",
            Operator::Equal => "==",
            Operator::NotEqual => "!=",
            Operator::GreaterThan => ">",
            Operator::GreaterThanOrEqual => ">=",
            Operator::LessThan => "<",
            Operator::LessThanOrEqual => "<=",
            Operator::And => "and",
            Operator::Or => "or",
            Operator::In => "in",
            Operator::NotIn => "not in",
            Operator::Contains => "contains",
            Operator::StartsWith => "startsWith",
            Operator::EndsWith => "endsWith",
            Operator::Matches => "matches",
        }
    }

    /// The operator a token spells, or `None` if it spells none.
    ///
    /// Both spellings of the logical operators are accepted, as the grammar allows both. `**`
    /// is handled by the caller, which is where the grammar's alias for `^` already lived.
    fn from_token(token: &str) -> Option<Self> {
        Some(match token {
            "+" => Operator::Add,
            "-" => Operator::Subtract,
            "*" => Operator::Multiply,
            "/" => Operator::Divide,
            "%" => Operator::Modulo,
            "^" => Operator::Pow,
            "==" => Operator::Equal,
            "!=" => Operator::NotEqual,
            ">" => Operator::GreaterThan,
            ">=" => Operator::GreaterThanOrEqual,
            "<" => Operator::LessThan,
            "<=" => Operator::LessThanOrEqual,
            "&&" | "and" => Operator::And,
            "||" | "or" => Operator::Or,
            "in" => Operator::In,
            "not in" => Operator::NotIn,
            "contains" => Operator::Contains,
            "startsWith" => Operator::StartsWith,
            "endsWith" => Operator::EndsWith,
            "matches" => Operator::Matches,
            _ => return None,
        })
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl From<Pair<'_, Rule>> for Operator {
    fn from(pair: Pair<Rule>) -> Self {
        trace!("[operator] {pair:?}");
        if pair.as_rule() == Rule::not_in_op {
            return Operator::NotIn;
        }
        match pair.as_str() {
            "**" => Operator::Pow,
            op => Operator::from_token(op)
                .unwrap_or_else(|| unreachable!("Invalid operator {op}")),
        }
    }
}

pub(crate) fn values_equal(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Integer(left), Float(right)) => *left as f64 == *right,
        (Float(left), Integer(right)) => *left == *right as f64,
        (Array(left), Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| values_equal(left, right))
        }
        (Map(left), Map(right)) => {
            left.len() == right.len()
                && left.iter().all(|(key, left)| {
                    right
                        .get(key)
                        .is_some_and(|right| values_equal(left, right))
                })
        }
        (KeyedMap(left), KeyedMap(right)) => {
            left.len() == right.len()
                && left.iter().all(|(left_key, left_value)| {
                    right.iter().any(|(right_key, right_value)| {
                        map_keys_equal(left_key, right_key)
                            && values_equal(left_value, right_value)
                    })
                })
        }
        _ => left == right,
    }
}

pub(crate) fn is_comparable_map_key(value: &Value) -> bool {
    !matches!(
        value,
        Array(_) | Bytes(_) | Map(_) | KeyedMap(_)
    )
}

pub(crate) fn map_keys_equal(left: &Value, right: &Value) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right) && left == right
}

impl Environment<'_> {
    pub fn eval_operator(
        &self,
        ctx: &dyn ContextProvider,
        operator: &Operator,
        left: &Node,
        right: &Node,
        #[cfg(feature = "regex")] compiled_regex: Option<&regex::Regex>,
    ) -> Result<Value> {
        let left = self.eval_expr(ctx, left)?;
        match &operator {
            Operator::And => {
                return match left {
                    Bool(false) => Ok(Bool(false)),
                    Bool(true) => match self.eval_expr(ctx, right)? {
                        Bool(value) => Ok(Bool(value)),
                        _ => bail!("Invalid operands for operator {operator}"),
                    },
                    _ => bail!("Invalid operands for operator {operator}"),
                };
            }
            Operator::Or => {
                return match left {
                    Bool(true) => Ok(Bool(true)),
                    Bool(false) => match self.eval_expr(ctx, right)? {
                        Bool(value) => Ok(Bool(value)),
                        _ => bail!("Invalid operands for operator {operator}"),
                    },
                    _ => bail!("Invalid operands for operator {operator}"),
                };
            }
            _ => {}
        }
        let right = self.eval_expr(ctx, right)?;
        let result = match operator {
            Operator::Add => match (left, right) {
                (Integer(left), Integer(right)) => left.wrapping_add(right).into(),
                (Float(left), Float(right)) => (left + right).into(),
                (Integer(left), Float(right)) => Float(left as f64 + right),
                (Float(left), Integer(right)) => Float(left + right as f64),
                (String(left), String(right)) => format!("{left}{right}").into(),
                #[cfg(feature = "temporal")]
                (DateTime(left), Duration(right)) => {
                    DateTime(left.checked_add_signed(chrono::Duration::nanoseconds(right))
                        .ok_or_else(|| crate::Error::ExprError("date out of range".into()))?)
                }
                #[cfg(feature = "temporal")]
                (Duration(left), DateTime(right)) => {
                    DateTime(right.checked_add_signed(chrono::Duration::nanoseconds(left))
                        .ok_or_else(|| crate::Error::ExprError("date out of range".into()))?)
                }
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => Duration(left.wrapping_add(right)),
                _ => bail!("Invalid operands for operator +"),
            },
            Operator::Subtract => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left.wrapping_sub(right)),
                (Float(left), Float(right)) => Float(left - right),
                (Integer(left), Float(right)) => Float(left as f64 - right),
                (Float(left), Integer(right)) => Float(left - right as f64),
                #[cfg(feature = "temporal")]
                (DateTime(left), DateTime(right)) => Duration(
                    (left - right)
                        .num_nanoseconds()
                        .ok_or_else(|| crate::Error::ExprError("duration out of range".into()))?,
                ),
                #[cfg(feature = "temporal")]
                (DateTime(left), Duration(right)) => {
                    DateTime(left.checked_sub_signed(chrono::Duration::nanoseconds(right))
                        .ok_or_else(|| crate::Error::ExprError("date out of range".into()))?)
                }
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => Duration(left.wrapping_sub(right)),
                _ => bail!("Invalid operands for operator -"),
            },
            Operator::Multiply => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left.wrapping_mul(right)),
                (Float(left), Float(right)) => Float(left * right),
                (Integer(left), Float(right)) => Float(left as f64 * right),
                (Float(left), Integer(right)) => Float(left * right as f64),
                #[cfg(feature = "temporal")]
                (Duration(left), Integer(right)) => Duration(left.wrapping_mul(right)),
                #[cfg(feature = "temporal")]
                (Integer(left), Duration(right)) => Duration(left.wrapping_mul(right)),
                _ => bail!("Invalid operands for operator *"),
            },
            Operator::Divide => match (left, right) {
                (Integer(left), Integer(right)) => Float(left as f64 / right as f64),
                (Float(left), Float(right)) => Float(left / right),
                (Integer(left), Float(right)) => Float(left as f64 / right),
                (Float(left), Integer(right)) => Float(left / right as f64),
                _ => bail!("Invalid operands for operator /"),
            },
            Operator::Modulo => match (left, right) {
                (Integer(_), Integer(0)) => bail!("integer divide by zero"),
                (Integer(left), Integer(right)) => Integer(left.wrapping_rem(right)),
                _ => bail!("Invalid operands for operator %"),
            },
            Operator::Pow => match (left, right) {
                (Integer(left), Integer(right)) => Float((left as f64).powf(right as f64)),
                (Float(left), Float(right)) => Float(left.powf(right)),
                (Integer(left), Float(right)) => Float((left as f64).powf(right)),
                (Float(left), Integer(right)) => Float(left.powf(right as f64)),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::Equal => match (&left, &right) {
                #[cfg(feature = "temporal")]
                (Month(_) | Weekday(_), Integer(_))
                | (Integer(_), Month(_) | Weekday(_)) => {
                    bail!("Invalid operands for operator {operator}")
                }
                (Map(_), KeyedMap(_)) | (KeyedMap(_), Map(_)) => {
                    bail!("Invalid operands for operator {operator}")
                }
                _ => Bool(values_equal(&left, &right)),
            },
            Operator::NotEqual => match (&left, &right) {
                #[cfg(feature = "temporal")]
                (Month(_) | Weekday(_), Integer(_))
                | (Integer(_), Month(_) | Weekday(_)) => {
                    bail!("Invalid operands for operator {operator}")
                }
                (Map(_), KeyedMap(_)) | (KeyedMap(_), Map(_)) => {
                    bail!("Invalid operands for operator {operator}")
                }
                _ => Bool(!values_equal(&left, &right)),
            },
            Operator::GreaterThan => match (left, right) {
                (Integer(left), Integer(right)) => (left > right).into(),
                (Float(left), Float(right)) => (left > right).into(),
                (Integer(left), Float(right)) => (left as f64 > right).into(),
                (Float(left), Integer(right)) => (left > right as f64).into(),
                (String(left), String(right)) => (left > right).into(),
                #[cfg(feature = "temporal")]
                (DateTime(left), DateTime(right)) => (left > right).into(),
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => (left > right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::GreaterThanOrEqual => match (left, right) {
                (Integer(left), Integer(right)) => (left >= right).into(),
                (Float(left), Float(right)) => (left >= right).into(),
                (Integer(left), Float(right)) => (left as f64 >= right).into(),
                (Float(left), Integer(right)) => (left >= right as f64).into(),
                (String(left), String(right)) => (left >= right).into(),
                #[cfg(feature = "temporal")]
                (DateTime(left), DateTime(right)) => (left >= right).into(),
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => (left >= right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::LessThan => match (left, right) {
                (Integer(left), Integer(right)) => (left < right).into(),
                (Float(left), Float(right)) => (left < right).into(),
                (Integer(left), Float(right)) => ((left as f64) < right).into(),
                (Float(left), Integer(right)) => (left < right as f64).into(),
                (String(left), String(right)) => (left < right).into(),
                #[cfg(feature = "temporal")]
                (DateTime(left), DateTime(right)) => (left < right).into(),
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => (left < right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::LessThanOrEqual => match (left, right) {
                (Integer(left), Integer(right)) => (left <= right).into(),
                (Float(left), Float(right)) => (left <= right).into(),
                (Integer(left), Float(right)) => (left as f64 <= right).into(),
                (Float(left), Integer(right)) => (left <= right as f64).into(),
                (String(left), String(right)) => (left <= right).into(),
                #[cfg(feature = "temporal")]
                (DateTime(left), DateTime(right)) => (left <= right).into(),
                #[cfg(feature = "temporal")]
                (Duration(left), Duration(right)) => (left <= right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::And | Operator::Or => unreachable!("handled before evaluating right operand"),
            Operator::In => match (left, right) {
                (String(left), Map(right)) => right.contains_key(&left).into(),
                (left, KeyedMap(right)) => right
                    .iter()
                    .any(|(key, _)| map_keys_equal(&left, key))
                    .into(),
                (left, Array(right)) => right
                    .iter()
                    .any(|right| values_equal(&left, right))
                    .into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::NotIn => match (left, right) {
                (String(left), Map(right)) => (!right.contains_key(&left)).into(),
                (left, KeyedMap(right)) => (!right
                    .iter()
                    .any(|(key, _)| map_keys_equal(&left, key)))
                    .into(),
                (left, Array(right)) => (!right.iter().any(|right| values_equal(&left, right))).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::Contains => match (left, right) {
                (String(left), String(right)) => left.contains(&right).into(),
                (Array(left), right) => left
                    .iter()
                    .any(|left| values_equal(left, &right))
                    .into(),
                (Map(left), String(right)) => left.contains_key(&right).into(),
                _ => bail!("Invalid operands for operator contains"),
            },
            Operator::StartsWith => match (left, right) {
                (String(left), String(right)) => Bool(left.starts_with(&right)),
                _ => bail!("Invalid operands for operator startsWith"),
            },
            Operator::EndsWith => match (left, right) {
                (String(left), String(right)) => Bool(left.ends_with(&right)),
                _ => bail!("Invalid operands for operator endsWith"),
            },
            #[cfg(feature = "regex")]
            Operator::Matches => match (left, right) {
                (String(left), String(right)) => {
                    if let Some(regex) = compiled_regex {
                        Bool(regex.is_match(&left))
                    } else {
                        Bool(regex::Regex::new(&right)?.is_match(&left))
                    }
                }
                _ => bail!("Invalid operands for operator matches"),
            },
            // Reachable only because the grammar has no features: the operator parses, and
            // says what is missing rather than pretending the pattern did not match.
            #[cfg(not(feature = "regex"))]
            Operator::Matches => bail!("the `matches` operator requires the `regex` feature"),
        };

        Ok(result)
    }
}
