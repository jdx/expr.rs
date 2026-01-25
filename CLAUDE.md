# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Test Commands

```bash
cargo build           # Build the library
cargo test            # Run all tests
cargo test test_name  # Run a single test
cargo clippy          # Run linter
pestfmt src/expr.pest # Format the grammar file
mise lint             # Run full lint (clippy + pestfmt)
mise test             # Run lint + tests
```

## Architecture

This is a Rust implementation of the [expr](https://expr-lang.org/) expression language, published as the `expr-lang` crate (library name: `expr`).

### Core Pipeline

1. **Parsing** (`src/expr.pest`, `src/parser.rs`, `src/pratt.rs`): PEG grammar parsed by pest, then transformed into AST using a Pratt parser for operator precedence
2. **AST** (`src/ast/`): Expression tree with `Node` variants for values, identifiers, operations, functions, and postfix operations
3. **Evaluation** (`src/eval.rs`): Tree-walking interpreter that evaluates nodes against a `Context` (variable bindings)

### Key Types

- **`Value`** (`src/value.rs`): Runtime values - Number(i64), Float(f64), Bool, String, Array, Map, Nil
- **`Context`**: HashMap-like container for variable bindings passed to evaluation
- **`Environment`**: Holds custom function definitions; use `Environment::new()` for built-in functions
- **`Program`**: Compiled AST from `compile()`, can be reused for multiple evaluations

### Built-in Functions

Located in `src/functions/`:
- `string.rs`: String manipulation (upper, lower, trim, split, etc.)
- `array.rs`: Array operations (len, first, last, map, filter, etc.)
- `json.rs`: JSON encoding/decoding

### Adding Custom Functions

```rust
env.add_function("name", |call: ExprCall| {
    // call.args: Vec<Value>
    // call.predicate: Option<Program> (for closures like `filter(arr, {# > 0})`)
    // call.ctx, call.env: for nested evaluation
    Ok(result.into())
});
```

### Optional Features

- `serde`: Enables `to_value`/`from_value` for converting between Rust types and `Value`
