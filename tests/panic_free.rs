use expr::{Context, eval};

#[test]
fn malformed_builtin_calls_return_errors_without_panicking() {
    let context = Context::default();
    let expressions = [
        "trimPrefix()",
        "trimPrefix(1)",
        r#"trimPrefix("a", "b", "c")"#,
        "trimSuffix()",
        "split()",
        r#"split("a")"#,
        "splitAfter()",
        r#"indexOf("a")"#,
        r#"lastIndexOf("a")"#,
        r#"hasPrefix("a")"#,
        r#"hasSuffix("a")"#,
    ];

    for expression in expressions {
        let result = std::panic::catch_unwind(|| eval(expression, &context));
        assert!(result.is_ok(), "{expression:?} panicked");
        assert!(result.unwrap().is_err(), "{expression:?} unexpectedly succeeded");
    }
}

#[test]
fn split_after_handles_zero_and_negative_limits() {
    let context = Context::default();
    assert_eq!(
        eval(r#"splitAfter("a,b", ",", 0)"#, &context).unwrap(),
        expr::Value::Array(Vec::new())
    );
    assert_eq!(
        eval(r#"splitAfter("a,b", ",", -1)"#, &context).unwrap(),
        expr::Value::Array(vec!["a,".into(), "b".into()])
    );
}
