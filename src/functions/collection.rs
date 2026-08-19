use crate::{Environment, Value, bail};

fn one_array(name: &str, mut args: Vec<Value>) -> crate::Result<Vec<Value>> {
    if args.len() != 1 {
        bail!("{name}() takes exactly one argument");
    }
    match args.pop().expect("length checked") {
        Value::Array(values) => Ok(values),
        _ => bail!("{name}() takes an array as the argument"),
    }
}

fn flatten(values: Vec<Value>) -> Vec<Value> {
    let mut stack = values.into_iter().rev().collect::<Vec<_>>();
    let mut output = Vec::new();
    while let Some(value) = stack.pop() {
        match value {
            Value::Array(values) => stack.extend(values.into_iter().rev()),
            value => output.push(value),
        }
    }
    output
}

/// Add Go expr-compatible collection utility functions.
pub fn add_collection_functions(env: &mut Environment) {
    env.add_function("join", |call| {
        if call.args.is_empty() || call.args.len() > 2 {
            bail!("join() takes one or two arguments");
        }
        let separator = match call.args.get(1) {
            Some(Value::String(separator)) => separator.as_str(),
            Some(_) => bail!("join() separator must be a string"),
            None => "",
        };
        let Value::Array(values) = &call.args[0] else {
            bail!("join() takes an array as the first argument");
        };
        let values = values
            .iter()
            .map(|value| match value {
                Value::String(value) => Ok(value.as_str()),
                _ => bail!("join() array elements must be strings"),
            })
            .collect::<crate::Result<Vec<_>>>()?;
        Ok(Value::from(values.join(separator)))
    });

    env.add_function("first", |call| {
        Ok(one_array("first", call.args)?
            .into_iter()
            .next()
            .unwrap_or_default())
    });
    env.add_function("last", |call| {
        Ok(one_array("last", call.args)?
            .into_iter()
            .next_back()
            .unwrap_or_default())
    });
    env.add_function("take", |call| {
        if call.args.len() != 2 {
            bail!("take() takes exactly two arguments");
        }
        let Value::Array(values) = &call.args[0] else {
            bail!("take() takes an array as the first argument");
        };
        let Value::Integer(count) = call.args[1] else {
            bail!("take() takes an integer as the second argument");
        };
        let count = usize::try_from(count).map_err(|_| {
            crate::Error::ExprError("take() count cannot be negative".to_string())
        })?;
        Ok(Value::Array(
            values.iter().take(count).cloned().collect(),
        ))
    });
    env.add_function("reverse", |call| {
        let mut values = one_array("reverse", call.args)?;
        values.reverse();
        Ok(Value::Array(values))
    });
    env.add_function("uniq", |call| {
        let mut output = Vec::new();
        for value in one_array("uniq", call.args)? {
            if !output
                .iter()
                .any(|candidate| crate::ast::operator::values_equal(candidate, &value))
            {
                output.push(value);
            }
        }
        Ok(Value::Array(output))
    });
    env.add_function("concat", |call| {
        if call.args.is_empty() {
            bail!("concat() takes at least one argument");
        }
        let mut output = Vec::new();
        for value in call.args {
            match value {
                Value::Array(values) => output.extend(values),
                _ => bail!("concat() arguments must be arrays"),
            }
        }
        Ok(Value::Array(output))
    });
    env.add_function("flatten", |call| {
        let values = one_array("flatten", call.args)?;
        Ok(Value::Array(flatten(values)))
    });
}

#[cfg(test)]
mod tests {
    use super::flatten;
    use crate::Value;

    #[test]
    fn flatten_handles_deeply_nested_arrays_iteratively() {
        let mut value = Value::Integer(1);
        for _ in 0..20_000 {
            value = Value::Array(vec![value]);
        }
        assert_eq!(flatten(vec![value]), vec![Value::Integer(1)]);
    }
}
