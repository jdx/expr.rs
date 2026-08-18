use crate::{bail, Environment, Value};
use indexmap::IndexMap;

fn add_sum(total: Value, value: Value) -> crate::Result<Value> {
    match (total, value) {
        (Value::Integer(total), Value::Integer(value)) => Ok(Value::Integer(total + value)),
        (Value::Integer(total), Value::Float(value)) => Ok(Value::Float(total as f64 + value)),
        (Value::Float(total), Value::Integer(value)) => Ok(Value::Float(total + value as f64)),
        (Value::Float(total), Value::Float(value)) => Ok(Value::Float(total + value)),
        _ => bail!("sum() values must be numbers"),
    }
}

pub fn add_array_functions(env: &mut Environment) {
    env.add_function("count", |c| {
        if c.args.len() != 1 {
            bail!("count() takes exactly one array argument");
        }
        let Value::Array(values) = &c.args[0] else {
            bail!("count() takes an array as the first argument");
        };
        let mut count = 0;
        if let Some(predicate) = c.predicate {
            for value in values {
                match c
                    .env
                    .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    Value::Bool(true) => count += 1,
                    Value::Bool(false) => {}
                    _ => bail!("count() predicate must return a boolean"),
                }
            }
        } else {
            for value in values {
                match value {
                    Value::Bool(true) => count += 1,
                    Value::Bool(false) => {}
                    _ => bail!("count() without a predicate requires booleans"),
                }
            }
        }
        Ok(Value::Integer(count))
    });

    env.add_function("sum", |c| {
        if c.args.len() != 1 {
            bail!("sum() takes exactly one array argument");
        }
        let Value::Array(values) = &c.args[0] else {
            bail!("sum() takes an array as the first argument");
        };
        let mut total = Value::Integer(0);
        for value in values {
            let value = if let Some(predicate) = &c.predicate {
                c.env
                    .run_with_binding(predicate, c.ctx, "#", value.clone())?
            } else {
                value.clone()
            };
            total = add_sum(total, value)?;
        }
        Ok(total)
    });

    env.add_function("reduce", |c| {
        if c.args.is_empty() || c.args.len() > 2 {
            bail!("reduce() takes an array and optional initial value");
        }
        let Value::Array(values) = &c.args[0] else {
            bail!("reduce() takes an array as the first argument");
        };
        let Some(predicate) = c.predicate else {
            bail!("reduce() requires a predicate");
        };
        let (mut accumulator, start) = match c.args.get(1) {
            Some(initial) => (initial.clone(), 0),
            None => match values.first() {
                Some(first) => (first.clone(), 1),
                None => bail!("reduce() of an empty array requires an initial value"),
            },
        };
        for value in &values[start..] {
            accumulator = c.env.run_with_two_bindings(
                predicate,
                c.ctx,
                ("#", value.clone()),
                ("#acc", accumulator),
            )?;
        }
        Ok(accumulator)
    });

    env.add_function("all", |c| {
        if c.args.len() != 1 {
            bail!("all() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                if let Value::Bool(false) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(false.into());
                }
            }
            Ok(true.into())
        } else {
            bail!("all() takes an array as the first argument");
        }
    });

    env.add_function("any", |c| {
        if c.args.len() != 1 {
            bail!("any() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(true.into());
                }
            }
            Ok(false.into())
        } else {
            bail!("any() takes an array as the first argument");
        }
    });

    env.add_function("one", |c| {
        if c.args.len() != 1 {
            bail!("one() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            let mut found = false;
            for value in a {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    if found {
                        return Ok(false.into());
                    }
                    found = true;
                }
            }
            Ok(found.into())
        } else {
            bail!("one() takes an array as the first argument");
        }
    });

    env.add_function("none", |c| {
        if c.args.len() != 1 {
            bail!("none() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(false.into());
                }
            }
            Ok(true.into())
        } else {
            bail!("none() takes an array as the first argument");
        }
    });

    env.add_function("map", |c| {
        let mut result = Vec::new();
        if c.args.len() != 1 {
            bail!("map() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                result.push(c.env.run_with_binding(
                    predicate,
                    c.ctx,
                    "#",
                    value.clone(),
                )?);
            }
        } else {
            bail!("map() takes an array as the first argument");
        }
        Ok(result.into())
    });

    env.add_function("filter", |c| {
        let mut result = Vec::new();
        if c.args.len() != 1 {
            bail!("filter() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    result.push(value.clone());
                }
            }
        } else {
            bail!("filter() takes an array as the first argument");
        }
        Ok(result.into())
    });

    env.add_function("find", |c| {
        if c.args.len() != 1 {
            bail!("find() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(value.clone());
                }
            }
            Ok(Value::Nil)
        } else {
            bail!("find() takes an array as the first argument");
        }
    });

    env.add_function("findIndex", |c| {
        if c.args.len() != 1 {
            bail!("findIndex() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for (i, value) in a.iter().enumerate() {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(i.into());
                }
            }
            Ok(Value::Integer(-1))
        } else {
            bail!("findIndex() takes an array as the first argument");
        }
    });

    env.add_function("findLast", |c| {
        if c.args.len() != 1 {
            bail!("findLast() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for value in a.iter().rev() {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(value.clone());
                }
            }
            Ok(Value::Nil)
        } else {
            bail!("findLast() takes an array as the first argument");
        }
    });

    env.add_function("findLastIndex", |c| {
        if c.args.len() != 1 {
            bail!("findLastIndex() takes exactly one argument and a predicate");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            for (i, value) in a.iter().enumerate().rev() {
                if let Value::Bool(true) =
                    c.env
                        .run_with_binding(predicate, c.ctx, "#", value.clone())?
                {
                    return Ok(i.into());
                }
            }
            Ok(Value::Integer(-1))
        } else {
            bail!("findLastIndex() takes an array as the first argument");
        }
    });
    env.add_function("groupBy", |c| {
        if c.args.len() != 1 {
            bail!("groupBy() takes exactly two arguments");
        }
        if let (Value::Array(a), Some(predicate)) = (&c.args[0], c.predicate) {
            let mut groups = IndexMap::new();
            for value in a {
                if let Some(key) = c
                    .env
                    .run_with_binding(predicate, c.ctx, "#", value.clone())?
                    .as_string()
                {
                    groups.entry(key.to_string()).or_insert_with(Vec::new).push(value.clone());
                } else {
                    bail!("groupBy() predicate must return a string");
                }
            }
            Ok(Value::Map(groups.into_iter().map(|(k, group)| (k, group.into())).collect()))
        } else {
            bail!("groupBy() takes an array as the first argument and a predicate as the second argument");
        }
    });

    env.add_function("sort", |c| {
        if c.args.is_empty() || c.args.len() > 2 {
            bail!("sort() takes one or two arguments");
        }
        let Value::Array(a) = &c.args[0] else {
            bail!("sort() takes an array as the first argument");
        };
        let desc = if c.args.len() == 2 {
            match &c.args[1] {
                Value::String(s) if s == "desc" => true,
                Value::String(s) if s == "asc" => false,
                _ => bail!("sort() second argument must be \"asc\" or \"desc\""),
            }
        } else {
            false
        };
        let mut result = a.clone();
        result.sort_by(|a, b| {
            let cmp = match (a, b) {
                (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
                (Value::String(a), Value::String(b)) => a.cmp(b),
                (a, b) => a.to_string().cmp(&b.to_string()),
            };
            if desc {
                cmp.reverse()
            } else {
                cmp
            }
        });
        Ok(result.into())
    });

    env.add_function("sortBy", |c| {
        if c.args.is_empty() || c.args.len() > 2 {
            bail!("sortBy() takes one or two arguments and a predicate");
        }
        let Value::Array(a) = &c.args[0] else {
            bail!("sortBy() takes an array as the first argument");
        };
        let Some(predicate) = c.predicate else {
            bail!("sortBy() requires a predicate");
        };
        let desc = if c.args.len() == 2 {
            match &c.args[1] {
                Value::String(s) if s == "desc" => true,
                Value::String(s) if s == "asc" => false,
                _ => bail!("sortBy() second argument must be \"asc\" or \"desc\""),
            }
        } else {
            false
        };
        // Compute keys for each element
        let mut keyed: Vec<(Value, Value)> = Vec::new();
        for value in a {
            let key = c
                .env
                .run_with_binding(predicate, c.ctx, "#", value.clone())?;
            keyed.push((key, value.clone()));
        }
        keyed.sort_by(|(a, _), (b, _)| {
            let cmp = match (a, b) {
                (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
                (Value::String(a), Value::String(b)) => a.cmp(b),
                (a, b) => a.to_string().cmp(&b.to_string()),
            };
            if desc {
                cmp.reverse()
            } else {
                cmp
            }
        });
        Ok(keyed.into_iter().map(|(_, v)| v).collect::<Vec<_>>().into())
    });
}
