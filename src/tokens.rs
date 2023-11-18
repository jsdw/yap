//! The point of this library. This module contains the core [`Tokens`] trait, which adds
//! various convenience methods on top of an [`Iterator`] based interface aimed at making
//! it easy to parse things.
//!
//! The [`IntoTokens`] trait is also provided, and can be implemented for types that can be
//! converted into something implementing the [`Tokens`] trait (for example `&str` and `&[T]`).
mod many;
mod many_err;
mod sep_by;
mod sep_by_all;
mod sep_by_all_err;
mod sep_by_err;
mod slice;
mod take;
mod take_while;

use core::borrow::Borrow;
use core::ops::Deref;
use core::str::FromStr;

// Re-export the structs handed back from token fns:
pub use many::Many;
pub use many_err::ManyErr;
pub use sep_by::SepBy;
pub use sep_by_all::SepByAll;
pub use sep_by_all_err::SepByAllErr;
pub use sep_by_err::SepByErr;
pub use slice::Slice;
pub use take::Take;
pub use take_while::TakeWhile;

use crate::types::{WithContext, WithContextMut};

/// The tokens trait is an extension of the [`Iterator`] trait, and adds a bunch of useful methods
/// for parsing tokens from the underlying iterable type.
///
/// Implementations don't need to directly implement [`Iterator`]; instead there exists
/// [`Tokens::as_iter()`] and [`Tokens::into_iter()`] methods to return an iterator that is based
/// on the methods implemented here and keeps iterator methods in a separate namespace.
pub trait Tokens: Sized {
    /// The item returned from [`Tokens::next()`].
    type Item;

    /// An object which can be used to reset the token stream
    /// to some position.
    type Location: TokenLocation + PartialEq + core::fmt::Debug + Clone;

    /// Return the next token. This is also the basis of the [`Iterator`] implementation
    /// that's returned when you call [`Tokens::as_iter()`]. By implementing it here, we can keep
    /// all of the methods provided by [`Iterator`] in a separate "namespace" to avoid confusion
    /// and potential name collisions.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc".into_tokens();
    ///
    /// assert_eq!(s.next(), Some('a'));
    /// assert_eq!(s.next(), Some('b'));
    /// assert_eq!(s.next(), Some('c'));
    /// assert_eq!(s.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item>;

    /// Return a "location" pointer. This can be passed to [`Tokens::set_location`]
    /// to set the tokens location back to the state at the time it was handed out.
    /// If the [`crate::TokenLocation`] trait is in scope, you can also call the
    /// [`crate::TokenLocation::offset()`] method on it to obtain the current offset.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens, TokenLocation };
    ///
    /// let mut s = "abcde".into_tokens();
    ///
    /// let location = s.location();
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.location().offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.location().offset(), 2);
    ///
    /// s.set_location(location);
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.location().offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.location().offset(), 2);
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
    /// assert_eq!(s.is_at_location(&location), true);
    /// s.next();
    /// assert_eq!(s.is_at_location(&location), false);
    /// s.set_location(location);
    /// assert_eq!(s.is_at_location(&location), true);
    /// ```
    fn is_at_location(&self, location: &Self::Location) -> bool;

    /// Return an iterator over our tokens. The [`Tokens`] trait already mirrors the [`Iterator`]
    /// interface by providing [`Tokens::Item`] and [`Tokens::next()`], but we keep the [`Iterator`]
    /// separate to avoid collisions, and because some iterator methods don't consume tokens as you
    /// might expect, and so must be used with care when parsing input.
    fn as_iter(&'_ mut self) -> TokensAsIter<'_, Self> {
        TokensAsIter { tokens: self }
    }

    /// Like [`Tokens::as_iter()`], except it consumes `self`, which can be useful in some situations.
    fn into_iter(self) -> TokensIntoIter<Self> {
        TokensIntoIter { tokens: self }
    }

    /// Attempt to parse the remaining tokens into the first `Out` generic using [`str::parse()`].
    /// The second generic type may be used to buffer tokens, and can be any type that implements
    /// `FromIterator<Self::Item> + Deref<Target = str>`.
    ///
    /// If the parsing fails, then no tokens are consumed.
    ///
    /// As an optimisation, implementations may choose not to use the provided buffer type if they have a
    /// suitable internal buffer of their own already. This is the case for [`crate::types::StrTokens`].
    ///
    /// This is mostly expected to be used in conjunction with [`Tokens::take`] and [`Tokens::take_while`],
    /// which themselves return the matching [`Tokens`].
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut tokens = "123abc456".into_tokens();
    ///
    /// let n = tokens.take(3).parse::<u8, String>().unwrap();
    /// assert_eq!(n, 123);
    ///
    /// let s = tokens.take_while(|t| t.is_alphabetic()).parse::<String, String>().unwrap();
    /// assert_eq!(s, "abc".to_string());
    ///
    /// // This will fail to parse; the number is out of bounds. Failure will consume
    /// // no tokens.
    /// assert!(tokens.parse::<u8, String>().is_err());
    ///
    /// // This will work; the number can fit into a u16:
    /// let n2 = tokens.parse::<u16, String>().unwrap();
    /// assert_eq!(n2, 456);
    /// ```
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
    {
        self.optional_err(|toks| toks.collect::<Buf>().parse::<Out>())
    }

    /// This is called when `tokens.slice(..).parse()` is called, and exists so that `Tokens`
    /// impls have the chance to override/optimise this behaviour.
    ///
    /// This should never alter the location of the underlying tokens.
    #[doc(hidden)]
    fn parse_slice<Out, Buf>(
        &mut self,
        from: Self::Location,
        to: Self::Location,
    ) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
    {
        self.slice(from, to).collect::<Buf>().parse::<Out>()
    }

    /// This is called when `tokens.take_while(..).parse()` is called, and exists so that `Tokens`
    /// impls have the chance to override/optimise this behaviour.
    ///
    /// This should consume tokens on success, and consume nothing on failure.
    #[doc(hidden)]
    fn parse_take_while<Out, Buf, F>(&mut self, take_while: F) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
        F: FnMut(&Self::Item) -> bool,
    {
        self.optional_err(|toks| toks.take_while(take_while).collect::<Buf>().parse::<Out>())
    }

    /// This is called when `tokens.take(..).parse()` is called, and exists so that `Tokens`
    /// impls have the chance to override/optimise this behaviour.
    ///
    /// This should consume tokens on success, and consume nothing on failure.
    #[doc(hidden)]
    fn parse_take<Out, Buf>(&mut self, n: usize) -> Result<Out, <Out as FromStr>::Err>
    where
        Out: FromStr,
        Buf: FromIterator<Self::Item> + Deref<Target = str>,
    {
        self.optional_err(|toks| toks.take(n).collect::<Buf>().parse::<Out>())
    }

    /// Attach some context to your tokens. The returned struct, [`WithContext`], also implements
    /// [`Tokens`], and so has can be used in much the same way. Since this consumes your tokens, it's
    /// better suited to permanent context that you'd like throughout the parsing.
    ///
    /// See [`Tokens::with_context_mut`] for a version that's easier to attach temporary context with.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens, types::WithContext };
    ///
    /// fn skip_digits(toks: &mut WithContext<impl Tokens<Item=char>, usize>) {
    ///     let n_skipped = toks.skip_while(|c| c.is_digit(10));
    ///     *toks.context_mut() += n_skipped;
    /// }
    ///
    /// let mut tokens = "123abc456".into_tokens().with_context(0usize);
    ///
    /// skip_digits(&mut tokens);
    /// tokens.skip_while(|c| c.is_alphabetic());
    /// skip_digits(&mut tokens);
    ///
    /// assert_eq!(*tokens.context(), 6);
    /// ```
    fn with_context<C>(self, context: C) -> WithContext<Self, C> {
        WithContext::new(self, context)
    }

    /// Unlike [`Tokens::with_context`], which consumes the tokens, this borrows them mutably, allowing it to
    /// be used when you only have a mutable reference to tokens (which is a common function signature to use),
    /// and making it better suited to attaching temporary contexts.
    ///
    /// Be aware that if you attach context in a function called recursively, the type checker may shout at you
    /// for constructing a type like `WithContextMut<WithContextMut<WithContextMut<..>>>`. In these cases, you
    /// can "break the cycle" by removing the original `WithContextMut` by using
    /// [`crate::types::WithContextMut::into_parts()`] before wrapping the tokens in a new context for the recursive
    /// call.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn count_digit_comma_calls(toks: &mut impl Tokens<Item=char>) -> (u8, u8) {
    ///     let mut counts = (0u8, 0u8);
    ///     toks.with_context_mut(&mut counts).sep_by(
    ///         |t| {
    ///             t.context_mut().0 += 1;
    ///             let n_skipped = t.skip_while(|c| c.is_digit(10));
    ///             if n_skipped == 0 { None } else { Some(()) }
    ///         },
    ///         |t| {
    ///             t.context_mut().1 += 1;
    ///             t.token(',')
    ///         }
    ///     ).consume();
    ///     counts
    /// }
    ///
    /// let n: usize = 0;
    /// let mut tokens = "123,4,56,1,34,1".into_tokens();
    ///
    /// let (digits, seps) = count_digit_comma_calls(&mut tokens);
    ///
    /// assert_eq!(tokens.remaining().len(), 0);
    /// // digits parsed 6 times:
    /// assert_eq!(digits, 6);
    /// // Attempted to parse seps 6 times; failure on last ends it:
    /// assert_eq!(seps, 6);
    /// ```
    fn with_context_mut<C>(&mut self, context: C) -> WithContextMut<&mut Self, C> {
        WithContextMut::new(self, context)
    }

    /// Return a slice of tokens starting at the `to` location provided and ending just prior to
    /// the `from` location provided (ie equivalent to the range `to..from`).
    ///
    /// The slice returned from implements [`Tokens`], so you can use the full range
    /// of parsing functions on it.
    ///
    /// **Note:** the slice returned from this prevents the original tokens from being used until
    /// it's dropped, and resets the original tokens to their current location on `Drop`. if you
    /// [`core::mem::forget`] it, the original token location will equal whatever the slice location
    /// was when it was forgotten.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcdefghijklmnop".into_tokens();
    ///
    /// (0..5).for_each(|_| { s.next(); });
    /// let from = s.location();
    /// (0..5).for_each(|_| { s.next(); });
    /// let to = s.location();
    ///
    /// assert_eq!(s.next(), Some('k'));
    /// assert_eq!(s.next(), Some('l'));
    ///
    /// // Iterating the from..to range given:
    /// let vals: String = s.slice(from.clone(), to.clone()).collect();
    /// assert_eq!(&*vals, "fghij");
    ///
    /// // After the above is dropped, we can continue
    /// // from where we left off:
    /// assert_eq!(s.next(), Some('m'));
    /// assert_eq!(s.next(), Some('n'));
    ///
    /// // We can iterate this range again as we please:
    /// let vals: String = s.slice(from, to).collect();
    /// assert_eq!(&*vals, "fghij");
    ///
    /// // And the original remains unaffected..
    /// assert_eq!(s.next(), Some('o'));
    /// assert_eq!(s.next(), Some('p'));
    /// ```
    fn slice(&'_ mut self, from: Self::Location, to: Self::Location) -> Slice<'_, Self> {
        Slice::new(self, self.location(), from, to)
    }

    /// Return the current offset into the tokens that we've parsed up to so far.
    /// The exact meaning of this can vary by implementation; when parsing slices, it
    /// is index of the slice item we've consumed up to, and when
    /// parsing `&str`'s it is the number of bytes (not characters) consumed so far.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
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

    /// Return the next item in the input without consuming it.
    ///
    /// Prefer this to using the `peekable` iterator method, which consumes
    /// the tokens, and internally keeps hold of the peeked state itself.
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
        I: Borrow<Self::Item>,
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
        It::Item: Borrow<Self::Item>,
    {
        let location = self.location();

        // We don't `.zip()` here because we need to spot and handle the
        // case where we run out of self tokens before `ts` runs out, and reset
        // /return false in that situation.
        let ts_iter = ts.into_iter();
        for expected in ts_iter {
            match self.next() {
                Some(actual) => {
                    // We have a token; does it equal the expected one?
                    if &actual != expected.borrow() {
                        self.set_location(location);
                        return false;
                    }
                }
                None => {
                    // We ran out of tokens in self, so no match.
                    self.set_location(location);
                    return false;
                }
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
        It::Item: Borrow<Self::Item>,
    {
        for expected in ts.into_iter() {
            let location = self.location();
            match self.next() {
                Some(token) if &token == expected.borrow() => return Some(token),
                _ => {
                    self.set_location(location);
                }
            }
        }
        None
    }

    /// Return a [`Tokens`] impl that will take the next `n` tokens from the input (ending early
    /// if the input runs early).
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let digits: String = s.take(3).collect();
    /// assert_eq!(&*digits, "123");
    /// assert_eq!(s.remaining(), "45abc");
    /// ```
    fn take(&'_ mut self, n: usize) -> Take<'_, Self> {
        Take::new(self, n)
    }

    /// Return a [`Tokens`] impl that will consume tokens until the provided function returns false.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let digits: String = s.take_while(|c| c.is_numeric()).collect();
    /// assert_eq!(&*digits, "12345");
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    ///
    /// This exists primarily because [`Iterator::take_while()`] will consume the first token that
    /// does not match the predicate, which is often not what we'd want. The above example using
    /// [`Iterator::take_while()`] would look like:
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let digits: String = s.as_iter().take_while(|c| c.is_numeric()).collect();
    /// assert_eq!(&*digits, "12345");
    ///
    /// // Note that `Iterator::take_while` consumed the "a" in order to test it,
    /// // whereas `Tokens::take_while` did not:
    /// assert_eq!(s.remaining(), "bc");
    /// ```
    fn take_while<F>(&'_ mut self, f: F) -> TakeWhile<'_, Self, F>
    where
        F: FnMut(&Self::Item) -> bool,
    {
        TakeWhile::new(self, f)
    }

    /// Iterate over the tokens until the provided function returns false on one. Only consume the tokens
    /// that the function returned true for, returning the number of tokens that were consumed/skipped.
    /// Equivalent to `toks.take_while(f).count()`.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let n_skipped = s.skip_while(|c| c.is_numeric());
    ///
    /// assert_eq!(n_skipped, 5);
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    fn skip_while<F>(&mut self, f: F) -> usize
    where
        F: FnMut(&Self::Item) -> bool,
    {
        self.take_while(f).as_iter().count()
    }

    /// Returns a [`Tokens`] impl that runs the provided parser again and again, returning
    /// an output from it each time until it returns [`None`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit_pair(tokens: &mut impl Tokens<Item=char>) -> Option<u32> {
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
    fn many<F, Output>(&mut self, parser: F) -> Many<Self, F>
    where
        F: FnMut(&mut Self) -> Option<Output>,
    {
        Many::new(self, parser)
    }

    /// Returns a [`Tokens`] impl that runs the provided parser again and again, returning
    /// an output from it each time until it returns [`None`]. If the parser returns an error,
    /// no tokens will be consumed and the error will be returned as the final iteration.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Err { NotEnoughTokens, NotADigit(char) }
    /// fn parse_digit_pair(tokens: &mut impl Tokens<Item=char>) -> Result<u32, Err> {
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
    fn many_err<F, Output, E>(&'_ mut self, parser: F) -> ManyErr<'_, Self, F>
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
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
    /// fn parse_abc(tokens: &mut impl Tokens<Item=char>) -> Option<ABC> {
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
    fn skip_many<F>(&mut self, mut parser: F) -> usize
    where
        F: FnMut(&mut Self) -> bool,
    {
        self.many(|t| parser(t).then_some(())).as_iter().count()
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
    /// fn parse_abc(tokens: &mut impl Tokens<Item=char>) -> Option<ABC> {
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
    /// let mut s = "abcabcabcxyz".into_tokens();
    /// let skipped = s.skip_many1(|t| parse_abc(t).ok_or("aaah"));
    ///
    /// assert_eq!(skipped, Ok(3));
    /// assert_eq!(s.remaining(), "xyz");
    ///
    /// let mut s = "ababababcabc".into_tokens();
    /// let skipped = s.skip_many1(|t| parse_abc(t).ok_or("aaah"));
    ///
    /// assert_eq!(skipped, Err("aaah"));
    /// assert_eq!(s.remaining(), "ababababcabc");
    /// ```
    fn skip_many1<F, E, Ignored>(&mut self, parser: F) -> Result<usize, E>
    where
        F: FnMut(&mut Self) -> Result<Ignored, E>,
    {
        let mut toks = self.many_err(parser);
        // Return error if immediate fail:
        if let Some(Err(e)) = toks.next() {
            return Err(e);
        }
        // Else just consume whatever we can and count it all up.
        // Note: the last iteration of `many_err` will return an Error
        // and not a value, so where we'd otherwise `+1` this count to
        // account for the `iter.next()` above, we don't have to.
        let n_skipped = toks.as_iter().count();
        Ok(n_skipped)
    }

    /// Return a [`Tokens`] impl that parses anything matching the first `parser` function,
    /// and expects to parse something matching the second `separator` function between each
    /// of these.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(tokens: &mut impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1,2,3,4,abc".into_tokens();
    /// let digits: Vec<u32> = s.sep_by(|t| parse_digit(t), |t| t.token(',')).collect();
    /// assert_eq!(digits, vec![1,2,3,4]);
    /// assert_eq!(s.remaining(), ",abc");
    /// ```
    fn sep_by<F, S, Output>(&'_ mut self, parser: F, separator: S) -> SepBy<'_, Self, F, S>
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> bool,
    {
        SepBy::new(self, parser, separator)
    }

    /// Return a [`Tokens`] impl that parses anything matching the `parser` function, and expects
    /// to parse something matching the `separator` function between each one. Unlike [`Tokens::sep_by`],
    /// this accepts parsers that return `Result`s, and returns the result on each iteration. Once
    /// an error is hit, `None` is returned thereafter.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Err { NoMoreTokens, NotADigit(char) }
    ///
    /// fn parse_digit(tokens: &mut impl Tokens<Item=char>) -> Result<u32, Err> {
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
    fn sep_by_err<F, S, E, Output>(
        &'_ mut self,
        parser: F,
        separator: S,
    ) -> SepByErr<'_, Self, F, S>
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> bool,
    {
        SepByErr::new(self, parser, separator)
    }

    /// Returns a [`Tokens`] impl that parses anything matching the `parser` function,
    /// and expects to parse something matching the `separator` function between each one.
    /// The [`Tokens`] impl hands back the output from both the `parser` and `separator`
    /// function, which means that they are both expected to return the same type.
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
    /// fn parse_op(tokens: &mut impl Tokens<Item=char>) -> Option<Op> {
    ///     match tokens.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    ///
    /// fn parse_digit(tokens: &mut impl Tokens<Item=char>) -> Option<u32> {
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
    fn sep_by_all<F, S, Output>(
        &'_ mut self,
        parser: F,
        separator: S,
    ) -> SepByAll<'_, Self, F, S, Output>
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> Option<Output>,
    {
        SepByAll::new(self, parser, separator)
    }

    /// Similar to [`Tokens::sep_by_all`], except that the [`Tokens`] impl returned also
    /// hands back the first error encountered when attempting to run our `parser`.
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
    /// fn parse_op(tokens: &mut impl Tokens<Item=char>) -> Option<Op> {
    ///     match tokens.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    ///
    /// fn parse_digit(tokens: &mut impl Tokens<Item=char>) -> Result<u32, Err> {
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
    fn sep_by_all_err<F, S, Output, E>(
        &'_ mut self,
        parser: F,
        separator: S,
    ) -> SepByAllErr<'_, Self, F, S, Output>
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> Option<Output>,
    {
        SepByAllErr::new(self, parser, separator)
    }

    /// Parse some tokens that are optionally surrounded by the result of a `surrounding` parser.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "   hello    ".into_tokens();
    ///
    /// let hello: String = s.surrounded_by(
    ///     |t| t.take_while(|c| c.is_ascii_alphabetic()).collect(),
    ///     |t| { t.skip_while(|c| c.is_ascii_whitespace()); }
    /// );
    ///
    /// assert_eq!(&*hello, "hello");
    /// assert_eq!(s.remaining(), "");
    /// ```
    fn surrounded_by<F, S, Output>(&mut self, parser: F, mut surrounding: S) -> Output
    where
        F: FnOnce(&mut Self) -> Output,
        S: FnMut(&mut Self),
    {
        surrounding(self);
        let res = parser(self);
        surrounding(self);
        res
    }

    /// Attempt to parse some output from the tokens. Returning `None`
    /// or `false` signifies that no match was found, and no tokens will
    /// be consumed. Otherwise, we'll return the match and consume the tokens.
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
    fn optional<F, Output>(&mut self, f: F) -> Output
    where
        F: FnOnce(&mut Self) -> Output,
        Output: crate::one_of::IsMatch,
    {
        let location = self.location();
        if let Some(output) = f(self).into_match() {
            output
        } else {
            self.set_location(location);
            crate::one_of::IsMatch::match_failure()
        }
    }

    /// Attempt to parse some output from the tokens, returning a `Result`.
    /// If the `Result` returned is `Err`, no tokens will be consumed.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "foobar".into_tokens();
    ///
    /// let res = s.optional_err(|s| {
    ///     let a = s.next();
    ///     let b = s.next();
    ///     if a == b {
    ///         Ok("yay")
    ///     } else {
    ///         Err("a and b don't match!")
    ///     }
    /// });
    ///
    /// // nothing consumed since Err returned from fn
    /// assert_eq!(s.remaining(), "foobar");
    /// assert!(res.is_err());
    ///
    /// let res = s.optional_err(|s| {
    ///     let a = s.next();
    ///     let b = s.next();
    ///     if a != b {
    ///         Ok((a, b))
    ///     } else {
    ///         Err("a and b match!")
    ///     }
    /// });
    ///
    /// // 2 chars consumed since Ok returned from fn
    /// assert_eq!(s.remaining(), "obar");
    /// assert_eq!(res, Ok((Some('f'), Some('o'))));
    /// ```
    fn optional_err<F, Output, Error>(&mut self, f: F) -> Result<Output, Error>
    where
        F: FnOnce(&mut Self) -> Result<Output, Error>,
    {
        let location = self.location();
        match f(self) {
            Ok(output) => Ok(output),
            Err(err) => {
                self.set_location(location);
                Err(err)
            }
        }
    }

    /// Checks next input is [`None`] and, if true, consumes the `None`.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::Tokens;
    /// use yap::types::IterTokens;
    /// use core::iter;
    ///
    /// // This will always return None; eof will consume it.
    /// let mut toks = IterTokens::new(iter::empty::<char>());
    ///
    /// assert_eq!(toks.eof(), true);
    /// assert_eq!(toks.offset(), 1);
    ///
    /// assert_eq!(toks.eof(), true);
    /// assert_eq!(toks.offset(), 2);
    ///
    /// // This will return a char; eof won't consume anything.
    /// let mut toks = IterTokens::new(iter::once('a'));
    ///
    /// assert_eq!(toks.eof(), false);
    /// assert_eq!(toks.offset(), 0);
    ///
    /// assert_eq!(toks.eof(), false);
    /// assert_eq!(toks.offset(), 0);
    /// ```
    fn eof(&mut self) -> bool {
        self.optional(|t| t.next().is_none().then_some(()))
            .is_some()
    }

    /// Consume all remaining tokens. This is expected to be used in conjunction
    /// with combinators like[`Tokens::take`] and [`Tokens::take_while`]. This is
    /// just a shorthand for `toks.as_iter().for_each(drop)`.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut toks = "abc123def".into_tokens();
    ///
    /// // Take won't do anything unless it's consumed:
    /// toks.take(3);
    /// assert_eq!(toks.remaining(), "abc123def");
    ///
    /// // This is the same as `toks.take(3).as_iter().for_each(drop);`
    /// toks.take(3).consume();
    /// assert_eq!(toks.remaining(), "123def");
    ///
    /// toks.take_while(|t| t.is_numeric()).consume();
    /// assert_eq!(toks.remaining(), "def");
    /// ```
    fn consume(&mut self) {
        self.as_iter().for_each(drop)
    }

    /// Collect up all of the tokens into something that implements
    /// [`FromIterator`]. If you'd like to call `str::parse` on the
    /// subsequent collection, then prefer [`Tokens::parse`], which can
    /// be more optimal in some cases.
    ///
    /// This is just a shorthand for calling `toks.as_iter().collect()`.
    fn collect<B: FromIterator<Self::Item>>(&mut self) -> B {
        self.as_iter().collect()
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

/// A trait that is implemented by anything which can be converted into an
/// object implementing the [`Tokens`] trait.
pub trait IntoTokens<Item> {
    /// The type that will be used to implement the [`Tokens`] interface.
    type Tokens: Tokens<Item = Item>;
    /// Convert self into a type which implements the [`Tokens`] interface.
    fn into_tokens(self) -> Self::Tokens;
}

/// This is returned from [`Tokens::as_iter()`], and exposes the standard iterator
/// interface and methods on our tokens.
pub struct TokensAsIter<'a, T> {
    tokens: &'a mut T,
}
impl<'a, T: Tokens> Iterator for TokensAsIter<'a, T> {
    type Item = T::Item;
    fn next(&mut self) -> Option<Self::Item> {
        self.tokens.next()
    }
}

/// This is returned from [`Tokens::into_iter()`], and exposes the standard iterator
/// interface and methods on our tokens.
pub struct TokensIntoIter<T> {
    tokens: T,
}
impl<T: Tokens> Iterator for TokensIntoIter<T> {
    type Item = T::Item;
    fn next(&mut self) -> Option<Self::Item> {
        self.tokens.next()
    }
}

#[cfg(all(test, feature = "std"))]
mod test {

    use crate::types::IterTokens;

    use super::*;

    #[derive(Debug, PartialEq)]
    struct AB;

    // A simple parser that looks for "ab" in an input token stream.
    // Notably, it doesn't try to rewind on failure. We expect the `many`
    // combinators to take care of that sort of thing for us as needed.
    fn parse_ab(t: &mut impl Tokens<Item = char>) -> Option<AB> {
        // match any sequence "ab".
        let a = t.next()?;
        let b = t.next()?;
        if a == 'a' && b == 'b' {
            Some(AB)
        } else {
            None
        }
    }

    // Similar to the above, except it reports a more specific reason for
    // failure.
    fn parse_ab_err(t: &mut impl Tokens<Item = char>) -> Result<AB, ABErr> {
        // match any sequence "ab".
        let a = t.next().ok_or(ABErr::NotEnoughTokens)?;
        let b = t.next().ok_or(ABErr::NotEnoughTokens)?;

        if a != 'a' {
            Err(ABErr::IsNotA)
        } else if b != 'b' {
            Err(ABErr::IsNotB)
        } else {
            Ok(AB)
        }
    }

    #[derive(Debug, PartialEq)]
    enum ABErr {
        NotEnoughTokens,
        IsNotA,
        IsNotB,
    }

    #[test]
    fn test_tokens_fails_if_eof() {
        let mut t = "hi".into_tokens();
        assert!(!t.tokens("hip".chars()));
    }

    #[test]
    #[allow(clippy::needless_collect)]
    fn test_many() {
        // No input:
        let mut t = "".into_tokens();
        let abs: Vec<_> = t.many(parse_ab).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 0);
        assert_eq!(rest, vec![]);

        // Invalid input after half is consumed:
        let mut t = "acabab".into_tokens();
        let abs: Vec<_> = t.many(parse_ab).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 0);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        // 3 valid and then 1 half-invalid:
        let mut t = "abababaa".into_tokens();
        let abs: Vec<_> = t.many(parse_ab).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a', 'a']);

        // End of tokens before can parse the fourth:
        let mut t = "abababa".into_tokens();
        let abs: Vec<_> = t.many(parse_ab).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    #[allow(clippy::needless_collect)]
    fn test_many_err() {
        // No input:
        let mut t = "".into_tokens();
        let abs: Vec<_> = t.many_err(parse_ab_err).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::NotEnoughTokens)]);
        assert_eq!(rest, vec![]);

        // Invalid input immediately:
        let mut t = "ccabab".into_tokens();
        let abs: Vec<_> = t.many_err(parse_ab_err).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::IsNotA)]);
        assert_eq!(rest, vec!['c', 'c', 'a', 'b', 'a', 'b']);

        // Invalid input after half is consumed:
        let mut t = "acabab".into_tokens();
        let abs: Vec<_> = t.many_err(parse_ab_err).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Err(ABErr::IsNotB)]);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        // 3 valid and then 1 half-invalid:
        let mut t = "abababaa".into_tokens();
        let abs: Vec<_> = t.many_err(parse_ab_err).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(abs, vec![Ok(AB), Ok(AB), Ok(AB), Err(ABErr::IsNotB)]);
        assert_eq!(rest, vec!['a', 'a']);

        // End of tokens before can parse the fourth:
        let mut t = "abababa".into_tokens();
        let abs: Vec<_> = t.many_err(parse_ab_err).collect();
        let rest: Vec<char> = t.collect();

        assert_eq!(
            abs,
            vec![Ok(AB), Ok(AB), Ok(AB), Err(ABErr::NotEnoughTokens)]
        );
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    fn test_skip_many() {
        let mut t = "".into_tokens();
        let n_skipped = t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(n_skipped, 0);
        assert_eq!(rest, vec![]);

        let mut t = "acabab".into_tokens();
        let n_skipped = t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(n_skipped, 0);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        let mut t = "ababaab".into_tokens();
        let n_skipped = t.skip_many(|t| parse_ab(t).is_some());
        let rest: Vec<char> = t.collect();
        assert_eq!(n_skipped, 2);
        assert_eq!(rest, vec!['a', 'a', 'b']);
    }

    #[test]
    fn test_skip_many1() {
        let mut t = "".into_tokens();
        let res = t.skip_many1(parse_ab_err);
        let rest: String = t.collect();
        assert_eq!(res, Err(ABErr::NotEnoughTokens));
        assert_eq!(&*rest, "");

        let mut t = "acabab".into_tokens();
        let res = t.skip_many1(parse_ab_err);
        let rest: String = t.collect();
        assert_eq!(res, Err(ABErr::IsNotB));
        assert_eq!(&*rest, "acabab");

        let mut t = "abcbab".into_tokens();
        let res = t.skip_many1(parse_ab_err);
        let rest: String = t.collect();
        assert_eq!(res, Ok(1));
        assert_eq!(&*rest, "cbab");

        let mut t = "ababcbab".into_tokens();
        let res = t.skip_many1(parse_ab_err);
        let rest: String = t.collect();
        assert_eq!(res, Ok(2));
        assert_eq!(&*rest, "cbab");
    }

    #[test]
    fn test_parse_optimisations() {
        // Our test string.
        const S: &str = "345abc456";

        fn parse_slice(mut tokens: impl Tokens<Item = char>) {
            // Get a start and end location to use:
            let from = tokens.location();
            tokens.take_while(|t| t.is_numeric()).consume();
            let to = tokens.location();
            tokens.set_location(from.clone());

            // This should work (nothing will be consumed)
            let n = tokens
                .parse_slice::<u16, String>(from.clone(), to.clone())
                .unwrap();
            assert_eq!(n, 345);
            assert_eq!(tokens.collect::<String>(), S);

            // reset location
            tokens.set_location(from.clone());

            // This won't work (again nothing will be consumed)
            tokens.parse_slice::<u8, String>(from, to).unwrap_err();
            assert_eq!(tokens.collect::<String>(), S);
        }

        fn parse_take_while(mut tokens: impl Tokens<Item = char>) {
            let start = tokens.location();

            // This should work
            let n = tokens
                .parse_take_while::<u16, String, _>(|t| t.is_numeric())
                .unwrap();
            assert_eq!(n, 345);
            assert_eq!(tokens.collect::<String>(), "abc456");

            // reset location
            tokens.set_location(start);

            // This wont work and won't consume anything
            tokens
                .parse_take_while::<u8, String, _>(|t| t.is_numeric())
                .unwrap_err();
            assert_eq!(tokens.collect::<String>(), "345abc456");
        }

        fn parse_take(mut tokens: impl Tokens<Item = char>) {
            let start = tokens.location();

            // This should work
            let n = tokens.parse_take::<u16, String>(3).unwrap();
            assert_eq!(n, 345);
            assert_eq!(tokens.collect::<String>(), "abc456");

            // reset location
            tokens.set_location(start);

            // This wont work and won't consume anything
            tokens.parse_take::<u8, String>(3).unwrap_err();
            assert_eq!(tokens.collect::<String>(), "345abc456");
        }

        // Test each method against our "optimised" StrTokens
        // and also the default impl of the methods via IterTokens

        parse_slice(IterTokens::new(S.chars()));
        parse_slice(S.into_tokens());

        parse_take_while(IterTokens::new(S.chars()));
        parse_take_while(S.into_tokens());

        parse_take(IterTokens::new(S.chars()));
        parse_take(S.into_tokens());
    }
}
