# Migrating from v1 to v2

Version 2 makes several intentional compatibility and API corrections. Most
callers only need to update the integer variant and accessor names.

## Integer values

`Value::Number` is now `Value::Integer`, and `Value::as_number()` is now
`Value::as_integer()`. This distinguishes integral values from `Value::Float`
without changing their `i64` representation.

```rust
let value = expr::Value::Integer(2);
assert_eq!(value.as_integer(), Some(2));
```

## Operator behavior

Mixed integer and float arithmetic, comparison, and equality now promote the
integer operand to a float. Logical `and` and `or` require boolean operands and
short-circuit evaluation. Code that relied on non-boolean truthiness must use an
explicit comparison instead.

The Go expr-compatible `bitand`, `bitor`, `bitxor`, `bitnand`, `bitnot`,
`bitshl`, `bitshr`, and `bitushr` functions are available in the default
environment.

## Borrowed contexts

Evaluation accepts `&dyn ContextProvider` rather than requiring `&Context`.
Existing calls that pass `&Context` do not need to change. `ExprCall::ctx` is
also a borrowed provider, so custom functions that previously cloned it should
look values up directly:

```rust
env.add_function("region", |call| {
    Ok(call.ctx.get("region").cloned().unwrap_or_default())
});
```

Call `call.ctx.to_context()` only when the custom function requires an owned
snapshot. Ordinary evaluation no longer clones the entire input context, and
`$env` materializes a snapshot only when referenced.

With the `serde` feature enabled, maps and structs can become contexts directly:

```rust
#[derive(serde::Serialize)]
struct Input<'a> {
    name: &'a str,
}

let context = expr::Context::from_serialize(&Input { name: "mise" })?;
# Ok::<(), expr::Error>(())
```

## Default environments

`Environment::default()` now behaves like `Environment::new()` and includes all
built-in functions. The deprecated `Parser::default()` receives the same fix.
Use an explicitly constructed custom environment if an empty function registry
is required.
