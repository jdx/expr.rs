# Go expr compatibility corpus

`cases.tsv` records expression results from Go expr v1.17.8, while
`errors.tsv` records expressions both implementations must reject. The Rust
integration tests evaluate expressions directly and compare structured JSON
values or error outcomes, independent of object key order.

After changing or adding cases, verify the expectations against the pinned Go
implementation:

```sh
cd compat
go run .
```

Then run the Rust side from the repository root:

```sh
cargo test --test go_compat
```
