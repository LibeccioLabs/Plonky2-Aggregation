/// measures the time needed to execute an expression.
///
/// It accepts two input formats:
/// - expr
/// - expr ; string_literal
///
/// When the input is just an expression, the output is
/// a tuple containing the evaluation of the expression,
/// followed by the time taken to evaluate it.
///
/// When the input also contains a string literal,
/// the literal is used to format an output message.
/// The format argument should contain just a `{:?}`
/// entry, used to print the time required to evaluate
/// the expression.
/// In this case, the macro evaluates to the input expression.
#[macro_export]
macro_rules! time_it {
    (
        $computation: expr;
        $output_format: literal
    ) => {{
        let (out, time) = $crate::time_it!($computation);
        println!($output_format, time);
        out
    }};

    ($computation: expr) => {{
        let start = std::time::Instant::now();
        let out = $computation;
        let end = std::time::Instant::now();
        (out, end - start)
    }};
}

pub enum RefOrValue<'r, T> {
    Ref(&'r T),
    Value(T),
}
