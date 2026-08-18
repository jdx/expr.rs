use crate::ast::node::Node;
use crate::Value::{Array, Bool, DateTime, Duration, Float, Integer, Map, Month, String, Weekday};
use crate::{bail, Result, Rule};
use crate::{ContextProvider, Environment, Value};
use log::trace;
use pest::iterators::Pair;
use std::str::FromStr;

#[derive(Debug, Clone, strum::EnumString, strum::Display)]
pub enum Operator {
    #[strum(serialize = "+")]
    Add,
    #[strum(serialize = "-")]
    Subtract,
    #[strum(serialize = "*")]
    Multiply,
    #[strum(serialize = "/")]
    Divide,
    #[strum(serialize = "%")]
    Modulo,
    #[strum(serialize = "^")]
    Pow,
    #[strum(serialize = "==")]
    Equal,
    #[strum(serialize = "!=")]
    NotEqual,
    #[strum(serialize = ">")]
    GreaterThan,
    #[strum(serialize = ">=")]
    GreaterThanOrEqual,
    #[strum(serialize = "<")]
    LessThan,
    #[strum(serialize = "<=")]
    LessThanOrEqual,
    #[strum(serialize = "&&", serialize = "and")]
    And,
    #[strum(serialize = "||", serialize = "or")]
    Or,
    #[strum(serialize = "in")]
    In,
    #[strum(serialize = "not in")]
    NotIn,
    #[strum(serialize = "contains")]
    Contains,
    #[strum(serialize = "startsWith")]
    StartsWith,
    #[strum(serialize = "endsWith")]
    EndsWith,
    #[strum(serialize = "matches")]
    Matches,
}

impl From<Pair<'_, Rule>> for Operator {
    fn from(pair: Pair<Rule>) -> Self {
        trace!("[operator] {pair:?}");
        if pair.as_rule() == Rule::not_in_op {
            return Operator::NotIn;
        }
        match pair.as_str() {
            "**" => Operator::Pow,
            op => Operator::from_str(op).unwrap_or_else(|_| unreachable!("Invalid operator {op}")),
        }
    }
}

fn values_equal(left: &Value, right: &Value) -> bool {
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
        _ => left == right,
    }
}

impl Environment<'_> {
    pub fn eval_operator(
        &self,
        ctx: &dyn ContextProvider,
        operator: &Operator,
        left: &Node,
        right: &Node,
        compiled_regex: Option<&regex::Regex>,
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
                (Integer(left), Integer(right)) => (left + right).into(),
                (Float(left), Float(right)) => (left + right).into(),
                (Integer(left), Float(right)) => Float(left as f64 + right),
                (Float(left), Integer(right)) => Float(left + right as f64),
                (String(left), String(right)) => format!("{left}{right}").into(),
                (DateTime(left), Duration(right)) => {
                    DateTime(left + chrono::Duration::nanoseconds(right))
                }
                (Duration(left), DateTime(right)) => {
                    DateTime(right + chrono::Duration::nanoseconds(left))
                }
                (Duration(left), Duration(right)) => Duration(left + right),
                _ => bail!("Invalid operands for operator +"),
            },
            Operator::Subtract => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left - right),
                (Float(left), Float(right)) => Float(left - right),
                (Integer(left), Float(right)) => Float(left as f64 - right),
                (Float(left), Integer(right)) => Float(left - right as f64),
                (DateTime(left), DateTime(right)) => Duration(
                    (left - right)
                        .num_nanoseconds()
                        .ok_or_else(|| crate::Error::ExprError("duration out of range".into()))?,
                ),
                (DateTime(left), Duration(right)) => {
                    DateTime(left - chrono::Duration::nanoseconds(right))
                }
                (Duration(left), Duration(right)) => Duration(left - right),
                _ => bail!("Invalid operands for operator -"),
            },
            Operator::Multiply => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left * right),
                (Float(left), Float(right)) => Float(left * right),
                (Integer(left), Float(right)) => Float(left as f64 * right),
                (Float(left), Integer(right)) => Float(left * right as f64),
                (Duration(left), Integer(right)) => Duration(left * right),
                (Duration(left), Float(right)) => Float(left as f64 * right),
                (Integer(left), Duration(right)) => Float(left as f64 * right as f64),
                (Float(left), Duration(right)) => Float(left * right as f64),
                _ => bail!("Invalid operands for operator *"),
            },
            Operator::Divide => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left / right),
                (Float(left), Float(right)) => Float(left / right),
                (Integer(left), Float(right)) => Float(left as f64 / right),
                (Float(left), Integer(right)) => Float(left / right as f64),
                (Duration(left), Integer(right)) => Float(left as f64 / right as f64),
                (Duration(left), Float(right)) => Float(left as f64 / right),
                (Duration(left), Duration(right)) => Float(left as f64 / right as f64),
                _ => bail!("Invalid operands for operator /"),
            },
            Operator::Modulo => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left % right),
                _ => bail!("Invalid operands for operator %"),
            },
            Operator::Pow => match (left, right) {
                (Integer(left), Integer(right)) => Integer(left.pow(right as u32)),
                (Float(left), Float(right)) => Float(left.powf(right)),
                (Integer(left), Float(right)) => Float((left as f64).powf(right)),
                (Float(left), Integer(right)) => Float(left.powf(right as f64)),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::Equal => match (&left, &right) {
                (Month(_) | Weekday(_), Integer(_))
                | (Integer(_), Month(_) | Weekday(_)) => {
                    bail!("Invalid operands for operator {operator}")
                }
                _ => Bool(values_equal(&left, &right)),
            },
            Operator::NotEqual => match (&left, &right) {
                (Month(_) | Weekday(_), Integer(_))
                | (Integer(_), Month(_) | Weekday(_)) => {
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
                (DateTime(left), DateTime(right)) => (left > right).into(),
                (Duration(left), Duration(right)) => (left > right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::GreaterThanOrEqual => match (left, right) {
                (Integer(left), Integer(right)) => (left >= right).into(),
                (Float(left), Float(right)) => (left >= right).into(),
                (Integer(left), Float(right)) => (left as f64 >= right).into(),
                (Float(left), Integer(right)) => (left >= right as f64).into(),
                (String(left), String(right)) => (left >= right).into(),
                (DateTime(left), DateTime(right)) => (left >= right).into(),
                (Duration(left), Duration(right)) => (left >= right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::LessThan => match (left, right) {
                (Integer(left), Integer(right)) => (left < right).into(),
                (Float(left), Float(right)) => (left < right).into(),
                (Integer(left), Float(right)) => ((left as f64) < right).into(),
                (Float(left), Integer(right)) => (left < right as f64).into(),
                (String(left), String(right)) => (left < right).into(),
                (DateTime(left), DateTime(right)) => (left < right).into(),
                (Duration(left), Duration(right)) => (left < right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::LessThanOrEqual => match (left, right) {
                (Integer(left), Integer(right)) => (left <= right).into(),
                (Float(left), Float(right)) => (left <= right).into(),
                (Integer(left), Float(right)) => (left as f64 <= right).into(),
                (Float(left), Integer(right)) => (left <= right as f64).into(),
                (String(left), String(right)) => (left <= right).into(),
                (DateTime(left), DateTime(right)) => (left <= right).into(),
                (Duration(left), Duration(right)) => (left <= right).into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::And | Operator::Or => unreachable!("handled before evaluating right operand"),
            Operator::In => match (left, right) {
                (String(left), Map(right)) => right.contains_key(&left).into(),
                (left, Array(right)) => right
                    .iter()
                    .any(|right| values_equal(&left, right))
                    .into(),
                _ => bail!("Invalid operands for operator {operator}"),
            },
            Operator::NotIn => match (left, right) {
                (String(left), Map(right)) => (!right.contains_key(&left)).into(),
                (left, Array(right)) => (!right.contains(&left)).into(),
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
        };

        Ok(result)
    }
}
