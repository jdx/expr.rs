use crate::ast::node::Node;
use crate::Rule;
use crate::{bail, Result};
use crate::{ContextProvider, Environment, Value};
use log::trace;
use pest::iterators::Pair;
use std::iter::once;

#[derive(Debug, Clone, strum::Display)]
pub enum PostfixOperator {
    Index { idx: Box<Node>, optional: bool },
    Range(Option<i64>, Option<i64>),
    Default(Box<Node>),
    Pipe(Box<Node>),
    Ternary { left: Box<Node>, right: Box<Node> },
    Method { ident: String, args: Vec<Node> },
}

impl PostfixOperator {
    pub(crate) fn contains_hash_ident(&self) -> bool {
        match self {
            PostfixOperator::Index { idx, .. } => idx.contains_hash_ident(),
            PostfixOperator::Default(node) | PostfixOperator::Pipe(node) => {
                node.contains_hash_ident()
            }
            PostfixOperator::Ternary { left, right } => {
                left.contains_hash_ident() || right.contains_hash_ident()
            }
            PostfixOperator::Method { args, .. } => {
                args.iter().any(Node::contains_hash_ident)
            }
            PostfixOperator::Range(..) => false,
        }
    }
}

impl From<Pair<'_, Rule>> for PostfixOperator {
    fn from(pair: Pair<Rule>) -> Self {
        trace!("{:?}={}", pair.as_rule(), pair.as_str());
        match pair.as_rule() {
            Rule::index_op | Rule::membership_op => PostfixOperator::Index {
                idx: Box::new(pair.into_inner().into()),
                optional: false,
            },
            Rule::opt_index_op | Rule::opt_membership_op => PostfixOperator::Index {
                idx: Box::new(pair.into_inner().into()),
                optional: true,
            },
            Rule::range_start_op => {
                let mut inner = pair.into_inner();
                let start = inner.next().map(|p| p.as_str().parse().unwrap());
                let end = inner.next().map(|p| p.as_str().parse().unwrap());
                PostfixOperator::Range(start, end)
            }
            Rule::range_end_op => {
                let mut inner = pair.into_inner();
                let end = inner.next().map(|p| p.as_str().parse().unwrap());
                PostfixOperator::Range(None, end)
            }
            Rule::default_op => PostfixOperator::Default(Box::new(pair.into_inner().into())),
            Rule::ternary => {
                let mut inner = pair.into_inner();
                let left = Box::new(inner.next().unwrap().into());
                let right = Box::new(inner.next().unwrap().into());
                PostfixOperator::Ternary { left, right }
            }
            Rule::pipe => PostfixOperator::Pipe(Box::new(pair.into_inner().into())),
            Rule::method_call => {
                let mut inner = pair.into_inner();
                PostfixOperator::Method {
                    ident: inner.next().expect("method name").as_str().to_string(),
                    args: inner.map(Node::from).collect(),
                }
            }
            rule => unreachable!("Unexpected rule: {rule:?}"),
        }
    }
}

impl Environment<'_> {
    pub fn eval_postfix_operator(
        &self,
        ctx: &dyn ContextProvider,
        operator: &PostfixOperator,
        node: &Node,
    ) -> Result<Value> {
        let value = self.eval_expr(ctx, node)?;
        let result = match operator {
            PostfixOperator::Index { idx, optional } => {
                let key = self.eval_index_key(ctx, idx)?;
                match (&key, value) {
                    (Value::Integer(idx), Value::Array(arr)) => {
                        let idx = i64_to_idx(*idx, arr.len());
                        arr.get(idx).cloned().unwrap_or(Value::Nil)
                    }
                    (Value::Integer(idx), Value::Bytes(bytes)) => {
                        let idx = i64_to_idx(*idx, bytes.len());
                        bytes
                            .get(idx)
                            .map(|byte| Value::Integer((*byte).into()))
                            .unwrap_or(Value::Nil)
                    }
                    (Value::String(key), Value::Map(map)) => {
                        map.get(key).cloned().unwrap_or(Value::Nil)
                    }
                    (key, Value::KeyedMap(map)) => map
                        .into_iter()
                        .find(|(candidate, _)| crate::ast::operator::values_equal(key, candidate))
                        .map(|(_, value)| value)
                        .unwrap_or(Value::Nil),
                    (_, _) if *optional => Value::Nil,
                    _ => bail!("Invalid operand for operator []: {key:?}"),
                }
            },
            PostfixOperator::Range(start, end) => match value {
                Value::Array(arr) => {
                    let (start, end) = slice_bounds(*start, *end, arr.len());
                    let result = arr.get(start..end).unwrap_or_default().to_vec();
                    Value::Array(result)
                }
                Value::Bytes(bytes) => {
                    let (start, end) = slice_bounds(*start, *end, bytes.len());
                    Value::Bytes(bytes.get(start..end).unwrap_or_default().to_vec())
                }
                _ => bail!("Invalid operand for operator []"),
            },
            PostfixOperator::Default(default) => match value {
                Value::Nil => self.eval_expr(ctx, default)?,
                value => value,
            },
            PostfixOperator::Ternary { left, right } => match value {
                Value::Bool(true) => self.eval_expr(ctx, left)?,
                Value::Bool(false) => self.eval_expr(ctx, right)?,
                value => bail!("Invalid condition for ?: {value:?}"),
            },
            PostfixOperator::Pipe(func) => {
                if let Node::Func {
                    ident,
                    args,
                    predicate,
                } = func.as_ref()
                {
                    let args = once(Ok(value))
                        .chain(args.iter().map(|arg| self.eval_expr(ctx, arg)))
                        .collect::<Result<Vec<Value>>>()?;
                    self.eval_func(ctx, ident, args, predicate.as_deref())?
                } else {
                    bail!("Invalid operand for operator |");
                }
            }
            PostfixOperator::Method { ident, args } => {
                let args = args
                    .iter()
                    .map(|arg| self.eval_expr(ctx, arg))
                    .collect::<Result<Vec<_>>>()?;
                crate::functions::temporal::eval_method(value, ident, args)?
            }
        };

        Ok(result)
    }

    fn eval_index_key(&self, ctx: &dyn ContextProvider, idx: &Node) -> Result<Value> {
        match idx {
            Node::Value(v) => Ok(v.clone()),
            Node::Ident(id) => Ok(Value::String(id.clone())),
            idx => self.eval_expr(ctx, idx),
        }
    }
}

fn i64_to_idx(idx: i64, len: usize) -> usize {
    if idx < 0 {
        (len as i64 + idx) as usize
    } else {
        idx as usize
    }
}

fn slice_idx(idx: i64, len: usize) -> usize {
    if idx < 0 {
        len.saturating_sub(idx.unsigned_abs() as usize)
    } else {
        usize::try_from(idx).unwrap_or(usize::MAX).min(len)
    }
}

fn slice_bounds(start: Option<i64>, end: Option<i64>, len: usize) -> (usize, usize) {
    let start = slice_idx(start.unwrap_or(0), len);
    let end = slice_idx(end.unwrap_or(len as i64), len);
    (start.min(end), end)
}
