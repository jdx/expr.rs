# Go expr compatibility corpus

`cases.tsv` records expression results from Go expr v1.17.8. Both runners
evaluate the expressions directly and compare their results as JSON values, so
object key order does not affect compatibility checks.

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
