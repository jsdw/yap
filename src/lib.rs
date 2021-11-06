mod tokens;

pub mod types;
pub use tokens::{ Tokens, IntoTokens };

/**
Given some tokens (a `&str` or a slice of items) and a parser function, return
the result of running the parser over the tokens.

This is a simple wrapper around just writing a parser function and passing it the
tokens you'd like to pass, so instead of writing:

```rust
use yap::{ Tokens, IntoTokens };

fn parser(mut t: impl Tokens<char>) -> Option<bool> {
    let a = t.next()?;
    let b = t.next()?;
    Some(a == 'a' && b == 'b')
}

let mut tokens = "abc".into_tokens();
let is_ab = parser(&mut tokens);
# assert_eq!(is_ab, Some(true));
# assert_eq!(tokens.next(), Some('c'));
```

We can write:

```rust
use yap::Tokens;

fn parser(mut t: impl Tokens<char>) -> Option<bool> {
    let a = t.next()?;
    let b = t.next()?;
    Some(a == 'a' && b == 'b')
}

let is_ab = yap::parse("abc", |t| parser(t).ok_or(()));
# assert_eq!(is_ab, Ok(true));
```

This is intended as an easily discoverable entry point into the parsing library; pick 
whatever approach you prefer.
*/
pub fn parse<Item, Output, T, F, E>(toks: T, mut parser: F) -> Result<Output, E>
where
    T: IntoTokens<Item>,
    F: FnMut(<T as IntoTokens<Item>>::Tokens) -> Result<Output, E>
{
    parser(toks.into_tokens())
}
