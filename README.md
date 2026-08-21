## expr-lang

Implementation of [expr](https://expr-lang.org/) in rust.

## Project status

`expr-lang` is actively maintained for use in [mise](https://mise.jdx.dev/) and
other Rust applications.

`expr-lang` implements expr syntax and built-ins with Go-compatible runtime
semantics and a small embeddable Rust API.

Go-specific reflection and static type checking are not implemented. Rust
strings must contain valid UTF-8, so string slices that split a Unicode code
point use the replacement character instead of preserving invalid bytes.

See [MIGRATION.md](MIGRATION.md) when upgrading from v1.

## Usage

```rust
use expr::{Context, Environment, self};

fn main() {
    let mut ctx = Context::default();
    ctx.insert("two".to_string(), 2);

    let three: i64 = expr::eval("1 + two", &ctx).unwrap().as_integer().unwrap();
    assert_eq!(three, 3);

    let mut env = Environment::new();
    env.add_function("add", |c| {
        let mut sum = 0;
        for arg in c.args {
            sum += arg.as_integer().unwrap();
        }
        Ok(sum.into())
    });

    let six: i64 = env.eval("add(1, two, 3)", &ctx).unwrap().as_integer().unwrap();
    assert_eq!(six, 6);
}
```

### Cargo features

Everything is on by default, so nothing changes for a dependent that says nothing. What the
features are for is the other direction: an embedder that knows which builtins its expressions
use can leave out the crates behind the rest. A CLI validating flag values with
`int(value) > 0` does not need a timezone database.

| Feature    | Default | What it enables                                                         | Crates it costs |
| ---------- | :-----: | ----------------------------------------------------------------------- | --------------: |
| `temporal` |   yes   | `now`, `date`, `duration`, `timezone`, every `.Year()`-style method, and the datetime/duration/timezone/month/weekday values | 7 |
| `json`     |   yes   | `fromJSON`, `toJSON` (implies `base64`, which is how `toJSON` writes bytes) | 4 |
| `regex`    |   yes   | the `matches` operator                                                  | 4 |
| `base64`   |   yes   | `toBase64`, `fromBase64`                                                | 1 |
| `serde`    |   no    | `to_value` / `from_value`, and `Serialize`/`Deserialize` for `Value`    | — |

```toml
# The evaluator, the operators, and every builtin that needs no crate to implement.
expr-lang = { version = "2", default-features = false }
```

That is 14 crates instead of 30. `keys`, `values`, `len`, the string and array builtins, the
arithmetic and comparison operators, and `?:` / `??` / pipes are all in the base: they need
nothing but the parser.

The grammar has no features, so an expression using a disabled builtin still parses — and says
which feature it needs rather than looking like a typo or a wrong answer:

```
fromJSON() requires expr-lang's `json` feature
the `matches` operator requires the `regex` feature
```

### Serde integration

#### Converting expr values to/from rust types

```toml
[dependencies]
expr-lang = { version = "2", features = ["serde"] }
serde = { version = "1.0", features = ["derive"] }
```

```rust
use expr::{Value, to_value, from_value};
use serde::{Deserialize, Serialize};

#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct Foo {
    a: i64,
    b: String,
}

fn main() {
    let foo = Foo {
        a: 1,
        b: "hello".to_string(),
    };

    let value: Value = to_value(&foo).unwrap();
    let map = value.as_map().unwrap();
    assert_eq!(map.get("a"), Some(&Value::Integer(1)));
    assert_eq!(map.get("b"), Some(&Value::String("hello".to_string())));
    assert_eq!(from_value::<Foo>(value).unwrap(), foo);
}
```

#### Converting expr values to/from serial data

```toml
[dependencies]
expr-lang = { version = "2", features = ["serde"] }
serde_json = "1.0"
```

```rust
use expr::Value;
use serde_json::{from_str, to_string};

fn main() {
    let json = r#"{
        "a": 1,
        "b": "hello"
    }"#;

    let value: Value = from_str(json).unwrap();
    let map = value.as_map().unwrap();
    assert_eq!(map.get("a"), Some(&Value::Integer(1)));
    assert_eq!(map.get("b"), Some(&Value::String("hello".to_string())));
    assert_eq!(to_string(&value).unwrap(), r#"{\"a\":1,\"b\":\"hello\"}"#);
}
```
