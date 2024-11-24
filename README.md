## expr-lang

Implementation of [expr](https://expr-lang.org/) in rust.

## Usage

```rust
use expr::ExprParser;

fn main() {
    let p = ExprParser::default();
    assert_eq!(p.eval("1 + 2").unwrap().to_string(), "3");
}
```
