/// Pass the provided tokens into each expression, one after the other.
/// Return the first not-`None` result.
///
/// # Examples
///
/// A basic example:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// // The macro expects a mutable reference to your tokens:
/// let ts = &mut tokens;
/// let res = yap::one_of!(ts;
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
/// You can declare an alias from some expression that's passed in, too.
/// Handy for abbreviating, or in this case, adding the required mut
/// reference:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res = yap::one_of!(ts from &mut tokens;
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
/// If an expression returns `None`, no tokens will be consumed:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res: Option<()> = yap::one_of!(ts from &mut tokens;
///     // This explicit iteration will be rewound if None is returned:
///     { ts.next(); ts.next(); None },
/// );
///
/// assert_eq!(tokens.remaining(), "hello world");
/// # assert_eq!(res, None);
/// ```
#[macro_export]
macro_rules! one_of {
    ($tokens:ident; $( $e:expr ),+ $(,)?) => {{
        #[allow(clippy::all)]
        loop {
            $(
                let checkpoint = $tokens.location();
                {
                    let $tokens = &mut *$tokens;
                    if let Some(res) = $e {
                        break Some(res);
                    }
                }
                $tokens.set_location(checkpoint);
            )+
            break None;
        }
    }};
    ($alias:ident from $tokens:expr; $( $e:expr ),+ $(,)?) => {{
        #[allow(clippy::all)]
        loop {
            $(
                let checkpoint = $tokens.location();
                {
                    let $alias = &mut *$tokens;
                    if let Some(res) = $e {
                        break Some(res);
                    }
                }
                $tokens.set_location(checkpoint);
            )+
            break None;
        }
    }};
}

#[cfg(test)]
mod test {
    use crate::{IntoTokens, Tokens};

    #[test]
    fn should_produce_no_clippy_warnings() {
        let mut ts = "abc".into_tokens();

        fn produces_result(ts: &mut impl Tokens<Item = char>) -> Result<char, ()> {
            if ts.token('a') {
                Ok('a')
            } else {
                Err(())
            }
        }

        one_of!(ts from &mut ts;
            produces_result(ts).ok(),
        );
    }
}
