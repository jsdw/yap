//! This module contains the core [`Tokens`] trait, which adds various convenience methods
//! to the standard [`Iterator`] interface aimed at making it easy to parse the input.
//!
//! The [`IntoTokens`] trait is implemented for types that can be converted into something
//! implementing the [`Tokens`] trait (for example `&str` and `&[T]`).
mod many;
mod many_err;
mod tokens_while;
mod sep_by;
mod sep_by_err;
mod sep_by_all;
mod sep_by_all_err;

use std::borrow::Borrow;

// Re-export the structs handed back from  token fns:
pub use tokens_while::TokensWhile;
pub use many::Many;
pub use many_err::ManyErr;
pub use sep_by::SepBy;
pub use sep_by_err::SepByErr;
pub use sep_by_all::SepByAll;
pub use sep_by_all_err::SepByAllErr;

/// The tokens trait builds on the [`Iterator`] trait, and adds a bunch of useful methods
/// for parsing tokens from the underlying iterable type.
pub trait Tokens: Iterator {

    /// An object which can be used to reset the token stream 
    /// to some position.
    type Location: TokenLocation + PartialEq;

    /// Return a "location" pointer. This can be passed to [`Tokens::set_location`]
    /// to set the tokens location back to the state at the time it was handed out.
    /// If the [`crate::TokenLocation`] trait is in scope, you can also call the
    /// [`crate::TokenLocation::offset()`] method on it to obtain the current offset.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcde".into_tokens();
    ///
    /// let location = s.location();
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.offset(), 2);
    ///
    /// s.set_location(location);
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.offset(), 2);
    /// ```
    fn location(&self) -> Self::Location;

    /// Set the tokens to the location provided. See [`Tokens::location`].
    fn set_location(&mut self, location: Self::Location);

    /// Return true if the current cursor location matches the location given, or false
    /// otherwise.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    /// 
    /// let mut s = "abc".into_tokens();
    /// let location = s.location();
    /// assert_eq!(s.is_at_location(location), true);
    /// s.next();
    /// assert_eq!(s.is_at_location(location), false);
    /// s.set_location(location);
    /// assert_eq!(s.is_at_location(location), true);
    /// ```
    fn is_at_location(&self, location: Self::Location) -> bool;

    /// Return the current offset into the tokens that we've parsed up to so far.
    /// The exact meaning of this can vary by implementation; when parsing slices, it
    /// is index of the slice item we've consumed up to, and when
    /// parsing `&str`'s it is the number of bytes (not characters) consumed so far.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens, TokenLocation };
    /// 
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.offset(), 0);
    /// s.next();
    /// assert_eq!(s.offset(), 1);
    /// s.next();
    /// assert_eq!(s.offset(), 2);
    /// ```
    fn offset(&self) -> usize {
        self.location().offset()
    }

    /// Get back the next item in the input without consuming it.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.peek(), Some('a'));
    /// assert_eq!(s.peek(), Some('a'));
    /// ```
    fn peek(&mut self) -> Option<Self::Item> {
        let location = self.location();
        let item = self.next();
        self.set_location(location);
        item
    }

    /// Expect a specific token to be next. If the token is not found, the iterator is not 
    /// advanced.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.token(&'a'), true);
    /// assert_eq!(s.token(&'b'), true);
    /// assert_eq!(s.token('z'), false);
    /// assert_eq!(s.token('y'), false);
    /// assert_eq!(s.token('c'), true);
    /// ```
    fn token<I>(&mut self, t: I) -> bool
    where 
        Self::Item: PartialEq,
        I: Borrow<Self::Item>
    {
        let location = self.location();
        match self.next() {
            Some(item) if &item == t.borrow() => true,
            _ => {
                self.set_location(location);
                false
            }
        }
    }

    /// Expect a specific set of tokens to be next. If the tokens are not found, the iterator is not 
    /// advanced. Anything that implements `IntoIterator` with an `Item` type that can be borrowed to
    /// produce `&Item` can be provided as an input to this.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcdef".into_tokens();
    /// 
    /// assert_eq!(s.tokens("abc".chars()), true);
    /// assert_eq!(s.remaining(), "def");
    /// 
    /// assert_eq!(s.tokens("de".chars()), true);
    /// assert_eq!(s.remaining(), "f");
    /// ```
    fn tokens<It>(&mut self, ts: It) -> bool
    where 
        Self::Item: PartialEq,
        It: IntoIterator,
        It::Item: Borrow<Self::Item>
    {
        let location = self.location();
        // `ts` comes first to avoid consuming an extra item from self before 
        // realising that it's time to stop..
        for (expected, actual) in ts.into_iter().zip(self.into_iter()) {
            if &actual != expected.borrow() {
                self.set_location(location);
                return false;
            }
        }
        true
    }

    /// Return the first token that matches the tokens provided, or None if none of them
    /// match.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcdef".into_tokens();
    ///
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('a'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('b'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('c'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), None);
    /// assert_eq!(s.remaining(), "def");
    /// ```
    fn one_of_tokens<It>(&mut self, ts: It) -> Option<Self::Item>
    where 
        Self::Item: PartialEq,
        It: IntoIterator,
        It::Item: Borrow<Self::Item>
    {
        for expected in ts.into_iter() {
            let location = self.location();
            match self.next() {
                Some(token) if &token == expected.borrow() => {
                    return Some(token)
                },
                _ => {
                    self.set_location(location);
                }
            }
        }
        None
    }

    /// Return an iterator that will consume tokens until the provided function returns false.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let digits: String = s.tokens_while(|c| c.is_numeric()).collect();
    /// assert_eq!(&*digits, "12345");
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    fn tokens_while<'a, F>(&'a mut self, f: F) -> TokensWhile<'a, Self, F>
    where
        Self: Sized, 
        F: FnMut(&Self::Item) -> bool
    {
        TokensWhile::new(self, f)
    }

    /// Iterate over the tokens until the provided function returns false on one.
    /// Only consume the tokens that the function returned true for, ignoring them.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// s.skip_tokens_while(|c| c.is_numeric());
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    fn skip_tokens_while<F>(&mut self, f: F)
    where
        Self: Sized, 
        F: FnMut(&Self::Item) -> bool
    {
        self.tokens_while(f).last();
    }

    /// Iterate over the tokens until the provided function returns true on one.
    /// Only consume the tokens that the function returned false for, ignoring them.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc12345".into_tokens();
    /// s.skip_tokens_until(|c| c.is_numeric());
    /// assert_eq!(s.remaining(), "12345");
    /// ```
    fn skip_tokens_until<F>(&mut self, mut f: F)
    where
        Self: Sized, 
        F: FnMut(&Self::Item) -> bool
    {
        self.skip_tokens_while(|t| !f(t))
    }

    /// Returns an iterator that, on each iteration, attempts to run the provided parser
    /// on the remaining tokens. If the parser returns [`None`], no tokens will be consumed.
    ///
    /// # Example
    /// 
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit_pair(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let d1 = tokens.next()?;
    ///     let d2 = tokens.next()?;
    ///     // Return the result of adding the 2 digits we saw:
    ///     Some(d1.to_digit(10)? + d2.to_digit(10)?)
    /// }
    ///
    /// let mut s = "12345abcde".into_tokens();
    /// let digits: Vec<u32> = s.many(|t| parse_digit_pair(t)).collect();
    ///
    /// assert_eq!(digits, vec![3, 7]);
    /// assert_eq!(s.remaining(), "5abcde");
    /// ```
    fn many<'a, F, Output>(&'a mut self, parser: F) -> Many<'a, Self, F>
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Option<Output>
    {
        Many::new(self, parser)
    }

    /// Returns an iterator that, on each iteration, attempts to run the provided parser
    /// on the remaining tokens. If the parser returns an error, no tokens will be consumed
    /// and the error will be returned as the final iteration.
    ///
    /// # Example
    /// 
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Err { NotEnoughTokens, NotADigit(char) }
    /// fn parse_digit_pair(mut tokens: impl Tokens<Item=char>) -> Result<u32, Err> {
    ///     let n1 = tokens.next()
    ///         .ok_or(Err::NotEnoughTokens)
    ///         .and_then(|c| c.to_digit(10).ok_or(Err::NotADigit(c)))?;
    ///     let n2 = tokens.next()
    ///         .ok_or(Err::NotEnoughTokens)
    ///         .and_then(|c| c.to_digit(10).ok_or(Err::NotADigit(c)))?;
    ///     Ok(n1 + n2)
    /// }
    ///
    /// let mut s = "12345abcde".into_tokens();
    /// let mut digits_iter = s.many_err(|t| parse_digit_pair(t));
    ///
    /// assert_eq!(digits_iter.next(), Some(Ok(3)));
    /// assert_eq!(digits_iter.next(), Some(Ok(7)));
    /// assert_eq!(digits_iter.next(), Some(Err(Err::NotADigit('a'))));
    /// assert_eq!(digits_iter.next(), None);
    /// assert_eq!(s.remaining(), "5abcde");
    /// ```
    fn many_err<'a, F, Output, E>(&'a mut self, parser: F) -> ManyErr<'a, Self, F>
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Result<Output, E>
    {
        ManyErr::new(self, parser)
    }

    /// Ignore 0 or more instances of some parser.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// struct ABC;
    /// fn parse_abc(mut tokens: impl Tokens<Item=char>) -> Option<ABC> {
    ///     let a = tokens.next()?;
    ///     let b = tokens.next()?;
    ///     let c = tokens.next()?;
    ///     if a == 'a' && b == 'b' && c == 'c' {
    ///         Some(ABC)
    ///     } else {
    ///         None
    ///     }
    /// }
    ///
    /// let mut s = "abcabcababab".into_tokens();
    /// s.skip_many(|t| parse_abc(t).is_some());
    ///
    /// assert_eq!(s.remaining(), "ababab");
    /// ```
    fn skip_many<F>(&mut self, mut parser: F)
    where
        Self: Sized,
        F: FnMut(&mut Self) -> bool
    {
        self.many(|t| parser(t).then(|| ())).last();
    }

    /// Ignore 1 or more instances of some parser. If the provided parser
    /// fails immediately, return the error that it produced.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// struct ABC;
    /// fn parse_abc(mut tokens: impl Tokens<Item=char>) -> Option<ABC> {
    ///     let a = tokens.next()?;
    ///     let b = tokens.next()?;
    ///     let c = tokens.next()?;
    ///     if a == 'a' && b == 'b' && c == 'c' {
    ///         Some(ABC)
    ///     } else {
    ///         None
    ///     }
    /// }
    ///
    /// let mut s = "ababababcabc".into_tokens();
    /// let digits = s.skip_many1(|t| parse_abc(t).ok_or("aaah"));
    ///
    /// assert_eq!(digits, Err("aaah"));
    /// assert_eq!(s.remaining(), "ababababcabc");
    /// ```
    fn skip_many1<F, E, Ignored>(&mut self, parser: F) -> Result<(), E> 
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Result<Ignored, E>
    {
        let mut iter = self.many_err(parser);
        // Return error if immediate fail:
        if let Some(Err(e)) = iter.next() {
            return Err(e);
        }
        // Else just consume whatever we can:
        iter.last();
        Ok(())
    }

    /// Return an iterator that parses anything matching the `parser` function, and expects 
    /// to parse something matching the `separator` function between each one.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1,2,3,4,abc".into_tokens();
    /// let digits: Vec<u32> = s.sep_by(|t| parse_digit(t), |t| t.token(',')).collect();
    /// assert_eq!(digits, vec![1,2,3,4]);
    /// assert_eq!(s.remaining(), ",abc");
    /// ```
    fn sep_by<'a, F, S, Output>(&'a mut self, parser: F, separator: S) -> SepBy<'a, Self, F, S>
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> bool
    {
        SepBy::new(self, parser, separator)
    }

    /// Return an iterator that parses anything matching the `parser` function, and expects 
    /// to parse something matching the `separator` function between each one. Unlike [`Tokens::sep_by`],
    /// this accepts parsers that return `Result`s, and returns the result on each iteration. Once
    /// an error is hit, `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Err { NoMoreTokens, NotADigit(char) }
    /// 
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Result<u32, Err> {
    ///     let c = tokens.next().ok_or(Err::NoMoreTokens)?;
    ///     c.to_digit(10).ok_or(Err::NotADigit(c))
    /// }
    ///
    /// let mut s = "1,2,a,1,2,3".into_tokens();
    /// let mut digits_iter = s.sep_by_err(|t| parse_digit(t), |t| t.token(','));
    /// assert_eq!(digits_iter.next(), Some(Ok(1)));
    /// assert_eq!(digits_iter.next(), Some(Ok(2)));
    /// assert_eq!(digits_iter.next(), Some(Err(Err::NotADigit('a'))));
    /// assert_eq!(digits_iter.next(), None);
    /// assert_eq!(s.remaining(), ",a,1,2,3");
    /// ```
    fn sep_by_err<'a, F, S, E, Output>(&'a mut self, parser: F, separator: S) -> SepByErr<'a, Self, F, S>
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> bool
    {
        SepByErr::new(self, parser, separator)
    }

    /// Returns an iterator that parses anything matching the `parser` function, 
    /// and expects to parse something matching the `separator` function between each one.
    /// The iterator returns the output from both the `parser` and `separator` function,
    /// which means that they are expected to return the same type.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(PartialEq,Debug)]
    /// enum Op { Plus, Minus, Divide }
    /// #[derive(PartialEq,Debug)]
    /// enum OpOrDigit { Op(Op), Digit(u32) }
    ///
    /// fn parse_op(mut t: impl Tokens<Item=char>) -> Option<Op> {
    ///     match t.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1+2/3-4+abc".into_tokens();
    /// let output: Vec<_> = s.sep_by_all(
    ///     |t| parse_digit(t).map(OpOrDigit::Digit), 
    ///     |t| parse_op(t).map(OpOrDigit::Op)
    /// ).collect();
    /// 
    /// assert_eq!(output, vec![
    ///     OpOrDigit::Digit(1),
    ///     OpOrDigit::Op(Op::Plus),
    ///     OpOrDigit::Digit(2),
    ///     OpOrDigit::Op(Op::Divide),
    ///     OpOrDigit::Digit(3),
    ///     OpOrDigit::Op(Op::Minus),
    ///     OpOrDigit::Digit(4),
    /// ]);
    /// assert_eq!(s.remaining(), "+abc");
    /// ```
    fn sep_by_all<'a, F, S, Output>(&'a mut self, parser: F, separator: S) -> SepByAll<'a, Self, F, S, Output> 
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> Option<Output>
    {
        SepByAll::new(self, parser, separator)
    }
    
    /// Similar to [`Tokens::sep_by_all`], except that the iterator returned also hands back
    /// the first error encountered when attempting to run our `parser`.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(PartialEq,Debug)]
    /// enum Op { Plus, Minus, Divide }
    /// #[derive(PartialEq,Debug)]
    /// enum OpOrDigit { Op(Op), Digit(u32) }
    /// #[derive(Debug, PartialEq)]
    /// enum Err { NoMoreTokens, NotADigit(char) }
    ///
    /// fn parse_op(mut t: impl Tokens<Item=char>) -> Option<Op> {
    ///     match t.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    /// 
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Result<u32, Err> {
    ///     let c = tokens.next().ok_or(Err::NoMoreTokens)?;
    ///     c.to_digit(10).ok_or(Err::NotADigit(c))
    /// }
    ///
    /// let mut s = "1+2/3-4+abc".into_tokens();
    /// let output: Vec<_> = s.sep_by_all_err(
    ///     |t| parse_digit(t).map(OpOrDigit::Digit), 
    ///     |t| parse_op(t).map(OpOrDigit::Op)
    /// ).collect();
    /// 
    /// assert_eq!(output, vec![
    ///     Ok(OpOrDigit::Digit(1)),
    ///     Ok(OpOrDigit::Op(Op::Plus)),
    ///     Ok(OpOrDigit::Digit(2)),
    ///     Ok(OpOrDigit::Op(Op::Divide)),
    ///     Ok(OpOrDigit::Digit(3)),
    ///     Ok(OpOrDigit::Op(Op::Minus)),
    ///     Ok(OpOrDigit::Digit(4)),
    ///     Err(Err::NotADigit('a'))
    /// ]);
    /// assert_eq!(s.remaining(), "+abc");
    /// ```
    fn sep_by_all_err<'a, F, S, Output, E>(&'a mut self, parser: F, separator: S) -> SepByAllErr<'a, Self, F, S, Output> 
    where
        Self: Sized,
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> Option<Output>
    {
        SepByAllErr::new(self, parser, separator)
    }

    /// Parse some tokens optionally surrounded by the tokens consumed by the surrounding parser.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "   hello    ".into_tokens();
    ///
    /// let hello: String = s.surrounded_by(
    ///     |t| t.tokens_while(|c| c.is_ascii_alphabetic()).collect(),
    ///     |t| t.skip_tokens_while(|c| c.is_ascii_whitespace())
    /// );
    ///
    /// assert_eq!(&*hello, "hello");
    /// assert_eq!(s.remaining(), "");
    /// ```
    fn surrounded_by<F, S, Output>(&mut self, mut parser: F, mut surrounding: S) -> Output 
    where
        F: FnMut(&mut Self) -> Output,
        S: FnMut(&mut Self)
    {
        self.skip_optional(&mut surrounding);
        let res = parser(self);
        self.skip_optional(&mut surrounding);
        res
    }

    /// Attempt to parse some output from the tokens. If the function returns `None`,
    /// don't consume any input. Else, return whatever the function produced.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "foobar".into_tokens();
    ///
    /// let res = s.optional(|s| {
    ///     let a = s.next();
    ///     let b = s.next();
    ///     if a == b {
    ///         Some("yay")
    ///     } else {
    ///         None
    ///     }
    /// });
    ///
    /// // nothing consumed since None returned from fn
    /// assert_eq!(s.remaining(), "foobar");
    /// assert_eq!(res, None);
    ///
    /// let res = s.optional(|s| {
    ///     let a = s.next()?;
    ///     let b = s.next()?;
    ///     Some((a, b))
    /// });
    ///
    /// // 2 chars consumed since Some returned from fn
    /// assert_eq!(s.remaining(), "obar");
    /// assert_eq!(res, Some(('f', 'o')));
    /// ```
    fn optional<F, Output>(&mut self, mut f: F) -> Option<Output> 
    where F: FnMut(&mut Self) -> Option<Output> {
        let location = self.location();
        match f(self) {
            Some(output) => Some(output),
            None => {
                self.set_location(location);
                None
            }
        }
    }

    /// Run a parser against some tokens, and don't care whether it succeeded
    /// or how much input it consumed.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "   helloworld".into_tokens();
    ///
    /// fn parse_whitespace(mut t: impl Tokens<Item=char>) {
    ///     t.skip_tokens_while(|c| c.is_ascii_whitespace());
    /// }
    ///
    /// s.skip_optional(|t| parse_whitespace(t));
    /// let is_hello = s.tokens("hello".chars());
    /// s.skip_optional(|t| parse_whitespace(t));
    /// let world: String = s.tokens_while(|c| c.is_ascii_alphabetic()).collect();
    ///
    /// // assert_eq!(is_hello, true);
    /// // assert_eq!(&*world, "world");
    /// ```
    fn skip_optional<F>(&mut self, mut f: F)
    where F: FnMut(&mut Self) {
        self.optional(|t| {
            f(t);
            Some(())
        });
    }

}

/// Calling [`Tokens::location()`] returns an object that implements this trait.
pub trait TokenLocation {
    /// Return the current offset into the tokens at the point at which this object 
    /// was created. [`Tokens::offset()`] is simply a shorthand for calling this method
    /// at the current location.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens, TokenLocation };
    /// 
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.location().offset(), 0);
    /// s.next();
    /// assert_eq!(s.location().offset(), 1);
    /// s.next();
    /// assert_eq!(s.location().offset(), 2);
    /// ```
    fn offset(&self) -> usize;
}

impl <'a, T> Tokens for &'a mut T 
where T: Tokens
{
    type Location = T::Location;

    fn location(&self) -> Self::Location {
        <T as Tokens>::location(self)
    }
    fn set_location(&mut self, location: Self::Location) {
        <T as Tokens>::set_location(self, location)
    }
    fn is_at_location(&self, location: Self::Location) -> bool {
        <T as Tokens>::is_at_location(self, location)
    }
}

/// A trait that is implemented by anything which can be converted into an 
/// object implementing the [`Tokens`] trait.
pub trait IntoTokens<Item> {
    type Tokens: Tokens<Item=Item>;
    fn into_tokens(self) -> Self::Tokens;
}


#[cfg(test)]
mod test {

    use super::*;

    #[derive(Debug, PartialEq)]
    struct AB;

    // A simple parser that looks for "ab" in an input token stream.
    // Notably, it doesn't try to rewind on failure. We expect the `many`
    // combinators to take care of that sort of thing for us as needed.
    fn parse_ab(mut t: impl Tokens<Item=char>) -> Option<AB> {
        // match any sequence "ab".
        let a = t.next()?;
        let b = t.next()?;
        if a == 'a' && b == 'b' {
            Some(AB)
        } else {
            None
        }
    }

    // Similar tot he above, except it reports a more specific reason for
    // failure.
    fn parse_ab_err(mut t: impl Tokens<Item=char>) -> Result<AB, ABErr> {
        // match any sequence "ab".
        let a = t.next().ok_or(ABErr::NotEnoughTokens)?;
        let b = t.next().ok_or(ABErr::NotEnoughTokens)?;

        if a != 'a' {
            Err(ABErr::NotA)
        } else if b != 'b' {
            Err(ABErr::NotB) 
        } else {
            Ok(AB)
        }
    }

    #[derive(Debug, PartialEq)]
    enum ABErr {
        NotEnoughTokens,
        NotA,
        NotB
    }

    #[test]
    fn test_many() {
        // No input:
        let mut t = "".into_tokens();
        let abs: Vec<_> = t.many(|t| parse_ab(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 0);
        assert_eq!(rest, vec![]);

        // Invalid input after half is consumed:
        let mut t = "acabab".into_tokens();
        let abs: Vec<_> = t.many(|t| parse_ab(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 0);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        // 3 valid and then 1 half-invalid:
        let mut t = "abababaa".into_tokens();
        let abs: Vec<_> = t.many(|t| parse_ab(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a', 'a']);

        // End of tokens before can parse the fourth:
        let mut t = "abababa".into_tokens();
        let abs: Vec<_> = t.many(|t| parse_ab(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    fn test_many_err() {
        // No input:
        let mut t = "".into_tokens();
        let abs: Vec<_> = t.many_err(|t| parse_ab_err(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::NotEnoughTokens)]);
        assert_eq!(rest, vec![]);

        // Invalid input immediately:
        let mut t = "ccabab".into_tokens();
        let abs: Vec<_> = t.many_err(|t| parse_ab_err(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::NotA)]);
        assert_eq!(rest, vec!['c', 'c', 'a', 'b', 'a', 'b']);

        // Invalid input after half is consumed:
        let mut t = "acabab".into_tokens();
        let abs: Vec<_> = t.many_err(|t| parse_ab_err(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::NotB)]);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        // 3 valid and then 1 half-invalid:
        let mut t = "abababaa".into_tokens();
        let abs: Vec<_> = t.many_err(|t| parse_ab_err(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Ok(AB), Ok(AB), Ok(AB), Err(ABErr::NotB)]);
        assert_eq!(rest, vec!['a', 'a']);

        // End of tokens before can parse the fourth:
        let mut t = "abababa".into_tokens();
        let abs: Vec<_> = t.many_err(|t| parse_ab_err(t)).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Ok(AB), Ok(AB), Ok(AB), Err(ABErr::NotEnoughTokens)]);
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    fn test_skip_many() {
        let mut t = "".into_tokens();
        t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(rest, vec![]);

        let mut t = "acabab".into_tokens();
        t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        let mut t = "ababaab".into_tokens();
        t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(rest, vec!['a', 'a', 'b']);
    }

    #[test]
    fn test_skip_many1() {
        let mut t = "".into_tokens();
        let res = t.skip_many1(|t| parse_ab_err(t));
        let rest: String = t.collect();
        assert_eq!(res, Err(ABErr::NotEnoughTokens));
        assert_eq!(&*rest, "");

        let mut t = "acabab".into_tokens();
        let res = t.skip_many1(|t| parse_ab_err(t));
        let rest: String = t.collect();
        assert_eq!(res, Err(ABErr::NotB));
        assert_eq!(&*rest, "acabab");

        let mut t = "ababcbab".into_tokens();
        let res = t.skip_many1(|t| parse_ab_err(t));
        let rest: String = t.collect();
        assert_eq!(res, Ok(()));
        assert_eq!(&*rest, "cbab");
    }

}