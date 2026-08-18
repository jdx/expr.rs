## expr-lang

Implementation of [expr](https://expr-lang.org/) in rust.

## Project status

`expr-lang` is actively maintained for use in [mise](https://mise.jdx.dev/) and
other Rust applications. The next release will be v2.

`expr-lang` implements the core expr syntax and built-ins used by mise. Version
2 targets Go-compatible runtime semantics and is expanding toward complete
expression-language parity. Go-specific reflection, static type checking,
optimization, and bytecode execution are outside that compatibility target.

Evaluation is currently tree-walking. Bytecode compilation is not planned for
v2; correctness, compatibility, and a small embeddable API take priority. A
bytecode backend could be considered later if real-world profiling shows that
evaluation itself is a bottleneck.

See [MIGRATION.md](MIGRATION.md) when upgrading from v1 to v2.

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

### Serde integration

#### Converting expr values to/from rust types

```toml
[dependencies]
expr-lang = { version = "1", features = ["serde"] }
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
expr-lang = { version = "1", features = ["serde"] }
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
