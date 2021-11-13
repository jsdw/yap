/// Pass the provided tokens into each function, one after the other.
/// Return the first not-`None` result.
///
/// # Examples
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res = yap::one_of!(tokens;
///     tokens.tokens("bye".chars()).then(|| 1),
///     tokens.tokens("hi".chars()).then(|| 2),
///     tokens.tokens("hello".chars()).then(|| 3),
///     tokens.tokens("world".chars()).then(|| 4),
/// );
///
/// assert_eq!(res, Some(3));
/// assert_eq!(tokens.remaining(), " world");
/// ```
///
/// You can also provide an alias to abbreviate the matches:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res = yap::one_of!(tokens as ts;
///     ts.tokens("bye".chars()).then(|| 1),
///     ts.tokens("hi".chars()).then(|| 2),
///     ts.tokens("hello".chars()).then(|| 3),
///     ts.tokens("world".chars()).then(|| 4),
/// );
///
/// assert_eq!(res, Some(3));
/// assert_eq!(tokens.remaining(), " world");
/// ```
///
/// This alias is simply a mutable borrow of the provided `tokens`, so that
/// after the macro is finished, you can continue using `tokens`.
///
/// If an expression returns `None`, no tokens will be consumed:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res: Option<()> = yap::one_of!(tokens as ts;
///     // This explicit iteration will be rewound if None is returned:
///     { ts.next(); ts.next(); None },
/// );
///
/// assert_eq!(tokens.remaining(), "hello world");
/// # assert_eq!(res, None);
/// ```
#[macro_export]
macro_rules! one_of {
    ($tokens:ident; $( $e:expr ),+ $(,)?) => {
        loop {
            $(
                let checkpoint = $tokens.location();
                if let Some(res) = $e {
                    break Some(res);
                }
                $tokens.set_location(checkpoint);
            )+
            break None;
        };
    };
    ($tokens:ident as $alias:ident; $( $e:expr ),+ $(,)?) => {
        loop {
            let mut $alias = &mut $tokens;
            $(
                let checkpoint = $alias.location();
                if let Some(res) = $e {
                    break Some(res);
                }
                $alias.set_location(checkpoint);
            )+
            break None;
        };
    }
}