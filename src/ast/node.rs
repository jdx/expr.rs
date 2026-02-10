use indexmap::IndexMap;
use crate::ast::operator::Operator;
use crate::ast::postfix_operator::PostfixOperator;
use crate::ast::unary_operator::UnaryOperator;
use crate::pratt::PRATT_PARSER;
use crate::{Rule, Value};
use log::trace;
use pest::iterators::{Pair, Pairs};
use crate::ast::program::Program;

#[derive(Debug, Clone)]
pub enum Node {
    Ident(String),
    Array(Vec<Node>),
    Range(Box<Node>, Box<Node>),
    Value(Value),
    Func { ident: String, args: Vec<Node>, predicate: Option<Box<Program>> },
    Unary {
        operator: UnaryOperator,
        node: Box<Node>,
    },
    Operation {
        operator: Operator,
        left: Box<Node>,
        right: Box<Node>,
    },
    Postfix {
        operator: PostfixOperator,
        node: Box<Node>,
    },
}

impl Node {
    /// Check if this node or any of its children reference the `#` variable
    pub(crate) fn contains_hash_ident(&self) -> bool {
        match self {
            Node::Ident(id) => id == "#",
            Node::Operation { left, right, .. } => {
                left.contains_hash_ident() || right.contains_hash_ident()
            }
            Node::Unary { node, .. } => node.contains_hash_ident(),
            Node::Postfix { node, operator } => {
                node.contains_hash_ident() || operator.contains_hash_ident()
            }
            Node::Func { args, predicate, .. } => {
                args.iter().any(|a| a.contains_hash_ident())
                    || predicate
                        .as_ref()
                        .map_or(false, |p| p.expr.contains_hash_ident())
            }
            Node::Array(items) => items.iter().any(|i| i.contains_hash_ident()),
            Node::Range(a, b) => a.contains_hash_ident() || b.contains_hash_ident(),
            Node::Value(_) => false,
        }
    }

    /// Functions that accept predicates (closures over `#`).
    /// Matches Go expr-lang's hardcoded predicates map in parser.go.
    fn accepts_predicate(name: &str) -> bool {
        matches!(
            name,
            "all" | "any" | "one" | "none" | "map" | "filter" | "find"
                | "findIndex" | "findLast" | "findLastIndex"
                | "count" | "sum" | "reduce" | "groupBy" | "sortBy"
        )
    }
}

impl Default for Node {
    fn default() -> Self {
        Node::Value(Value::default())
    }
}

impl From<Pairs<'_, Rule>> for Node {
    fn from(pairs: Pairs<Rule>) -> Self {
        PRATT_PARSER
            .map_primary(|primary| primary.into())
            .map_prefix(|operator, right| Node::Unary {
                operator: operator.into(),
                node: Box::new(right),
            })
            .map_postfix(|left, operator| Node::Postfix {
                operator: operator.into(),
                node: Box::new(left),
            })
            .map_infix(|left, operator, right| Node::Operation {
                operator: operator.into(),
                left: Box::new(left),
                right: Box::new(right),
            })
            .parse(pairs)
    }
}

impl From<Pair<'_, Rule>> for Node {
    fn from(pair: Pair<Rule>) -> Self {
        trace!("{:?} = {}", &pair.as_rule(), pair.as_str());
        match pair.as_rule() {
            Rule::expr => pair.into_inner().into(),
            Rule::value => Node::Value(pair.into_inner().into()),
            Rule::ident => Node::Ident(pair.as_str().to_string()),
            Rule::func => {
                let mut inner = pair.into_inner();
                let ident = inner.next().unwrap().as_str().to_string();
                let mut predicate = None;
                let mut args: Vec<Node> = Vec::new();
                for arg in inner {
                    match arg.as_rule() {
                        Rule::predicate => {
                            predicate = Some(Box::new(arg.into_inner().into()));
                        },
                        _ => {
                            args.push(arg.into());
                        },
                    }
                }
                // If no explicit predicate was parsed but the last arg references `#`,
                // promote it to the predicate. This matches Go expr-lang behavior where
                // `filter(arr, # > 2)` works without braces around the predicate.
                // Only applies to known predicate-accepting functions to avoid breaking
                // nested calls like `indexOf("abc", #)` inside braced predicates.
                // Uses >= 1 (not >= 2) so pipe syntax works: `arr | filter(# > 2)`.
                if predicate.is_none()
                    && !args.is_empty()
                    && Self::accepts_predicate(&ident)
                    && args.last().unwrap().contains_hash_ident()
                {
                    let last = args.pop().unwrap();
                    predicate = Some(Box::new(Program {
                        lines: Vec::new(),
                        expr: last,
                    }));
                }
                Node::Func { ident, args, predicate }
            },
            Rule::array => Node::Array(pair.into_inner().map(|p| p.into()).collect()),
            Rule::map => {
                let mut map = IndexMap::new();
                let vals = pair.clone();
                for (key, val) in pair
                    .into_inner()
                    .step_by(2)
                    .zip(vals.into_inner().skip(1).step_by(2))
                {
                    let key = key.as_str().to_string();
                    map.insert(key, val.into_inner().into());
                }
                Node::Value(Value::Map(map))
            }
            Rule::range => {
                let mut inner = pair.into_inner();
                let start = Box::new(inner.next().unwrap().into());
                let end = Box::new(inner.next().unwrap().into());
                Node::Range(start, end)
            }
            rule => unreachable!("Unexpected rule: {rule:?}"),
        }
    }
}
