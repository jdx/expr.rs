## expr-lang

Implementation of [expr](https://expr-lang.org/) in rust.

## Usage

```rust
use expr::{Context, Environment, self};

fn main() {
    let mut ctx = Context::default();
    ctx.insert("two".to_string(), 2);

    let three: i64 = expr::eval("1 + two", &ctx).unwrap().as_number().unwrap();
    assert_eq!(three, 3);

    let mut env = Environment::new();
    env.add_function("add", |c| {
        let mut sum = 0;
        for arg in c.args {
            sum += arg.as_number().unwrap();
        }
        Ok(sum.into())
    });

    let six: i64 = env.eval("add(1, two, 3)", &ctx).unwrap().as_number().unwrap();
    assert_eq!(six, 6);
}
```
