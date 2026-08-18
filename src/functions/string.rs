use crate::{bail, Environment, Value};

pub fn add_string_functions(env: &mut Environment) {
    env.add_function("trim", |c| {
        if c.args.len() != 1 && c.args.len() != 2 {
            bail!("trim() takes one or two arguments");
        }
        if let (Value::String(s), None) = (&c.args[0], c.args.get(1)) {
            Ok(s.trim().into())
        } else if let (Value::String(s), Some(Value::String(chars))) = (&c.args[0], c.args.get(1)) {
            Ok(s.trim_matches(|c| chars.contains(c)).into())
        } else {
            bail!("trim() takes a string as the first argument and an optional string of characters to trim");
        }
    });

    env.add_function("trimPrefix", |c| {
        if c.args.is_empty() || c.args.len() > 2 {
            bail!("trimPrefix() takes one or two arguments");
        }
        let Value::String(s) = &c.args[0] else {
            bail!("trimPrefix() takes a string as the first argument");
        };
        match c.args.get(1) {
            Some(Value::String(prefix)) => Ok(s.strip_prefix(prefix).unwrap_or(s).into()),
            None => Ok(s.into()),
            Some(_) => bail!("trimPrefix() prefix must be a string"),
        }
    });

    env.add_function("trimSuffix", |c| {
        if c.args.is_empty() || c.args.len() > 2 {
            bail!("trimSuffix() takes one or two arguments");
        }
        let Value::String(s) = &c.args[0] else {
            bail!("trimSuffix() takes a string as the first argument");
        };
        match c.args.get(1) {
            Some(Value::String(suffix)) => Ok(s.strip_suffix(suffix).unwrap_or(s).into()),
            None => Ok(s.into()),
            Some(_) => bail!("trimSuffix() suffix must be a string"),
        }
    });

    env.add_function("upper", |c| {
        if c.args.len() != 1 {
            bail!("upper() takes one argument");
        }
        if let Value::String(s) = &c.args[0] {
            Ok(s.to_uppercase().into())
        } else {
            bail!("upper() takes a string as the first argument");
        }
    });

    env.add_function("lower", |c| {
        if c.args.len() != 1 {
            bail!("lower() takes one argument");
        }
        if let Value::String(s) = &c.args[0] {
            Ok(s.to_lowercase().into())
        } else {
            bail!("lower() takes a string as the first argument");
        }
    });

    env.add_function("split", |c| {
        if c.args.len() != 2 && c.args.len() != 3 {
            bail!("split() takes two or three arguments");
        }
        if let (Value::String(s), Value::String(sep), None) = (&c.args[0], &c.args[1], c.args.get(2)) {
            Ok(s.split(sep).map(Value::from).collect::<Vec<_>>().into())
        } else if let (Value::String(s), Value::String(sep), Some(Value::Integer(n))) = (&c.args[0], &c.args[1], c.args.get(2)) {
            Ok(s.splitn(*n as usize, sep).map(Value::from).collect::<Vec<_>>().into())
        } else {
            bail!("split() takes a string as the first argument and a string as the second argument");
        }
    });

    env.add_function("splitAfter", |c| {
        if c.args.len() != 2 && c.args.len() != 3 {
            bail!("splitAfter() takes two or three arguments");
        }
        if let (Value::String(s), Value::String(sep), None) = (&c.args[0], &c.args[1], c.args.get(2)) {
            Ok(s.split_inclusive(sep).map(Value::from).collect::<Vec<_>>().into())
        } else if let (Value::String(s), Value::String(sep), Some(Value::Integer(n))) = (&c.args[0], &c.args[1], c.args.get(2)) {
            if *n == 0 {
                return Ok(Value::Array(Vec::new()));
            }
            if *n < 0 {
                return Ok(s.split_inclusive(sep).map(Value::from).collect::<Vec<_>>().into());
            }
            let count = *n as usize;
            let mut arr = s.split_inclusive(sep).take(count - 1).map(|s| s.to_string()).collect::<Vec<_>>();
            arr.push(s.split_inclusive(sep).skip(count - 1).collect::<Vec<_>>().join(""));
            Ok(arr.into())
        } else {
            bail!("splitAfter() takes a string as the first argument and a string as the second argument");
        }
    });

    env.add_function("replace", |c| {
        if c.args.len() != 3 && c.args.len() != 4 {
            bail!("replace() takes three or four arguments");
        }
        let (Value::String(s), Value::String(from), Value::String(to)) =
            (&c.args[0], &c.args[1], &c.args[2])
        else {
            bail!("replace() takes three strings");
        };
        match c.args.get(3) {
            None => Ok(s.replace(from, to).into()),
            Some(Value::Integer(count)) if *count < 0 => Ok(s.replace(from, to).into()),
            Some(Value::Integer(count)) => Ok(s.replacen(from, to, *count as usize).into()),
            Some(_) => bail!("replace() count must be an integer"),
        }
    });

    env.add_function("repeat", |c| {
        if c.args.len() != 2 {
            bail!("repeat() takes exactly two arguments");
        }
        let (Value::String(s), Value::Integer(count)) = (&c.args[0], &c.args[1]) else {
            bail!("repeat() takes a string and an integer");
        };
        let count = usize::try_from(*count)
            .map_err(|_| crate::Error::ExprError("repeat() count cannot be negative".into()))?;
        if count > 1_000_000 || s.len().checked_mul(count).is_none() {
            bail!("repeat() memory budget exceeded");
        }
        Ok(s.repeat(count).into())
    });

    env.add_function("indexOf", |c| {
        if c.args.len() != 2 {
            bail!("indexOf() takes exactly two arguments");
        }
        if let (Value::String(s), Value::String(sub)) = (&c.args[0], &c.args[1]) {
            Ok(s.find(sub).map(|i| i as i64).unwrap_or(-1).into())
        } else {
            bail!("indexOf() takes a string as the first argument and a string to search for as the second argument");
        }
    });

    env.add_function("lastIndexOf", |c| {
        if c.args.len() != 2 {
            bail!("lastIndexOf() takes exactly two arguments");
        }
        if let (Value::String(s), Value::String(sub)) = (&c.args[0], &c.args[1]) {
            Ok(s.rfind(sub).map(|i| i as i64).unwrap_or(-1).into())
        } else {
            bail!("lastIndexOf() takes a string as the first argument and a string to search for as the second argument");
        }
    });

    env.add_function("hasPrefix", |c| {
        if c.args.len() != 2 {
            bail!("hasPrefix() takes exactly two arguments");
        }
        if let (Value::String(s), Value::String(prefix)) = (&c.args[0], &c.args[1]) {
            Ok(s.starts_with(prefix).into())
        } else {
            bail!("hasPrefix() takes a string as the first argument and a string to search for as the second argument");
        }
    });

    env.add_function("hasSuffix", |c| {
        if c.args.len() != 2 {
            bail!("hasSuffix() takes exactly two arguments");
        }
        if let (Value::String(s), Value::String(suffix)) = (&c.args[0], &c.args[1]) {
            Ok(s.ends_with(suffix).into())
        } else {
            bail!("hasSuffix() takes a string as the first argument and a string to search for as the second argument");
        }
    });
}
