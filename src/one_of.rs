/// Pass the provided tokens into each expression, one after the other. All of the
/// expressions provided must return something implementing [`crate::one_of::IsMatch`],
/// ie `Option<T>` or `bool`. It will try each expression until a match is found,
/// consuming no tokens for any expressions that to not match.
///
/// - If expressions return `Option<T>`, then `Some(T)` denotes that we've found a match
///   and can return it, and `None` means that one_of should try the next expression.
/// - If expressions return `bool`, then returning true denotes that we've found a match
///   and returning `false` means to try the next expression.
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
/// We can return bools too, for when we want to find out whether something
/// matches but don't care what exactly has been matched:
///
/// ```
/// use yap::{ Tokens, IntoTokens };
///
/// let mut tokens = "hello world".into_tokens();
///
/// let res: bool = yap::one_of!(ts from &mut tokens;
///     ts.tokens("howdy".chars()),
///     ts.tokens("bye".chars()),
///     ts.tokens("hello".chars()),
/// );
///
/// assert_eq!(res, true);
/// assert_eq!(tokens.remaining(), " world");
/// ```
///
/// Expressions can return `Result`s inside the `Option` too (or anything else that they wish),
/// allowing for parsers to propagate errors out through this macro however you prefer.
#[macro_export]
macro_rules! one_of {
    ($tokens:ident; $( $e:expr ),+ $(,)?) => {{
        #[allow(clippy::all)]
        loop {
            $(
                let checkpoint = $tokens.location();
                {
                    let $tokens = &mut *$tokens;
                    if let Some(res) = $crate::one_of::IsMatch::into_match($e) {
                        break res
                    }
                }
                $tokens.set_location(checkpoint);
            )+
            break $crate::one_of::IsMatch::match_failure();
        }
    }};
    ($alias:ident from $tokens:expr; $( $e:expr ),+ $(,)?) => {{
        #[allow(clippy::all)]
        loop {
            $(
                let checkpoint = $tokens.location();
                {
                    let $alias = &mut *$tokens;
                    if let Some(res) = $crate::one_of::IsMatch::into_match($e) {
                        break res;
                    }
                }
                $tokens.set_location(checkpoint);
            )+
            break $crate::one_of::IsMatch::match_failure();
        }
    }};
}

/// Implementing this for some type allows the type to be returned from
/// expressions in [`crate::one_of!`], and [`crate::Tokens::optional`].
pub trait IsMatch: Sized {
    /// Return `Some(Self)` if `Self` denotes that we've found a
    /// match, and return `None` if `one_of` should try the next
    /// expression.
    fn into_match(self) -> Option<Self>;
    /// If `one_of` fails to find a match, it will return this.
    fn match_failure() -> Self;
}

// one_of can work with things that return bools;
// true means we found a match, and false means keep
// looking.
impl IsMatch for bool {
    fn into_match(self) -> Option<Self> {
        match self {
            true => Some(true),
            false => None,
        }
    }
    fn match_failure() -> Self {
        false
    }
}

// one_of can work with Options; Some(item) means
// that we found a match, and None means keep looking.
impl<T> IsMatch for Option<T> {
    fn into_match(self) -> Option<Self> {
        self.map(Some)
    }
    fn match_failure() -> Self {
        None
    }
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
