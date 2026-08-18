use expr::{Context, Value, compile, run};
use indexmap::IndexMap;
use std::hint::black_box;

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("startup") => {}
        Some("context") => context(),
        Some("predicate") => predicate(),
        Some("regex") => regex(),
        Some("json") => json(),
        scenario => panic!("unknown benchmark scenario: {scenario:?}"),
    }
}

fn context() {
    let ctx = Context::from_iter((0..10_000).map(|i| (format!("key_{i}"), i)));
    let program = compile("key_9999 + 1").unwrap();
    for _ in 0..100 {
        black_box(run(black_box(&program), black_box(&ctx)).unwrap());
    }
}

fn predicate() {
    let items = (0..500).map(Value::Integer).collect::<Vec<_>>();
    let ctx = Context::from_iter([("items", Value::Array(items))]);
    let program = compile("map(items, {# + 1})").unwrap();
    for _ in 0..10 {
        black_box(run(black_box(&program), black_box(&ctx)).unwrap());
    }
}

fn regex() {
    let ctx = Context::default();
    let program =
        compile(r#""release-2.0.0" matches "^release-[0-9]+\\.[0-9]+\\.[0-9]+$""#).unwrap();
    for _ in 0..10_000 {
        black_box(run(black_box(&program), black_box(&ctx)).unwrap());
    }
}

fn json() {
    let payload = (0..1_000)
        .map(|i| (format!("key_{i}"), Value::Integer(i)))
        .collect::<IndexMap<_, _>>();
    let ctx = Context::from_iter([("payload", Value::Map(payload))]);
    let program = compile("toJSON(payload)").unwrap();
    for _ in 0..100 {
        black_box(run(black_box(&program), black_box(&ctx)).unwrap());
    }
}
