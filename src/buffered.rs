//! Collecting tokens into temporary buffers.

use crate::Tokens;
use core::{
    array, iter,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// This is returned from [`Tokens::as_buffered()`], and exposes methods
/// requiring temporary allocations on our tokens.
pub struct BufferedTokens<'a, T, Buf> {
    pub(crate) tokens: &'a mut T,
    pub(crate) buf: PhantomData<Buf>,
}

impl<'a, T, Buf> BufferedTokens<'a, T, Buf>
where
    T: Tokens,
    Buf: FromIterator<T::Item> + Deref<Target = str>,
{
    /// Use [`str::parse`] to parse the next `n` elements.
    /// [`None`] if this is 0 elements.
    pub fn parse_n<O>(&mut self, n: usize) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let to_parse = self.tokens.as_iter().take(n).collect::<Buf>();
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }

    /// Use [`str::parse`] to parse the remaining elements until the next [`None`].
    /// [`None`] if this is 0 elements.
    pub fn parse_remaining<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let to_parse = self.tokens.as_iter().collect::<Buf>();
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }

    /// Use [`str::parse`] to parse the next chunk of input matching a predicate.
    /// [`None`] if this is 0 elements.
    pub fn parse_while<O, F>(&mut self, take_while: F) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
        F: FnMut(&T::Item) -> bool,
    {
        let to_parse = self.tokens.tokens_while(take_while).collect::<Buf>();
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }
}

impl<'a, T, Buf> BufferedTokens<'a, T, Buf>
where
    T: Tokens<Item = char>,
    Buf: FromIterator<T::Item> + Deref<Target = str>,
{
    /// Parse digits.
    pub fn digit<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_numeric())
    }

    /// Parses digits with a sign (`+`/`-`) in front.
    pub fn signed_digit<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let loc = self.tokens.location();
        let sign = self.tokens.next()?;
        match sign {
            '+' | '-' => {
                let to_parse = iter::once(sign)
                    .chain(self.tokens.tokens_while(|&t| t.is_numeric()))
                    .collect::<Buf>();
                (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
            }
            _ => {
                self.tokens.set_location(loc);
                None
            }
        }
    }

    /// Parses alphabetical characters.
    pub fn alpha<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_alphabetic())
    }

    /// Parses alphanumeric characters.
    pub fn alphanumeric<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_alphanumeric())
    }
}

/// A type that can collect [`u8`] on the stack to be used to [`str::parse`].
/// Requires a max buffer size at compile time.
/// # Panics
/// - Collecting more items than the buffer's max size causes a panic.
/// - Invalid-Utf8 will panic when dereferencing to a [`str`].
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StackString<const N: usize> {
    buf: [u8; N],
    len: usize,
}

impl<const N: usize> Default for StackString<N> {
    fn default() -> Self {
        Self {
            buf: array::from_fn(|_| Default::default()),
            len: Default::default(),
        }
    }
}

impl<I: Into<u8>, const N: usize> FromIterator<I> for StackString<N> {
    /// Creates a [`StackString`] from an iterator.
    /// # Panics
    /// Panics if the iterator is longer than the internal buffer of the [`StackString`]
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        let mut out = Self::default();
        for (i, val) in iter.into_iter().enumerate() {
            assert!(i < N, "Iterator longer than max buffer length ({N})");
            out.buf[i] = val.into();
            out.len += 1;
        }
        out
    }
}

impl<const N: usize> Deref for StackString<N> {
    type Target = str;

    /// Dereferences the stack string to a `&str`.
    /// # Panics
    /// - If the [`StackString`] holds invalid Utf8.
    fn deref(&self) -> &Self::Target {
        core::str::from_utf8(&self.buf[..self.len]).expect("Valid Utf8")
    }
}

impl<const N: usize> DerefMut for StackString<N> {
    /// Dereferences the stack string to a `&mut str`.
    /// # Panics
    /// - If the [`StackString`] holds invalid Utf8.
    fn deref_mut(&mut self) -> &mut Self::Target {
        core::str::from_utf8_mut(&mut self.buf[..self.len]).expect("Valid Utf8")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{types::IterTokens, IntoTokens};

    #[test]
    #[cfg(feature = "std")]
    fn parse_string() {
        let a: String = "123🗻∈🌏"
            .into_tokens()
            .as_buffered::<String>()
            .parse_remaining()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, "123🗻∈🌏");
    }

    #[test]
    #[cfg(feature = "std")]
    fn parse_unsigned() {
        let a: u8 = ("123🗻∈🌏".into_tokens())
            .as_buffered::<String>()
            .digit()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 123);
    }

    #[test]
    #[cfg(feature = "std")]
    fn parse_signed() {
        let a: u8 = "+123"
            .into_tokens()
            .as_buffered::<String>()
            .parse_n(3)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 12);
        let a: i8 = "+123"
            .into_tokens()
            .as_buffered::<String>()
            .parse_n(3)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 12);
        let a: i8 = "-123"
            .into_tokens()
            .as_buffered::<String>()
            .signed_digit()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123);
    }

    #[test]
    fn parse_stack() {
        let a: i32 = IterTokens::into_tokens("-123456789🗻∈🌏".bytes())
            .as_buffered::<StackString<10>>()
            .parse_n(10)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123456789);
        let a: i32 = IterTokens::into_tokens("-123456789🗻∈🌏".bytes())
            .as_buffered::<StackString<20>>()
            .parse_n(10)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123456789);
    }

    #[test]
    fn parse_empty() {
        assert!(IterTokens::into_tokens("".bytes())
            .as_buffered::<StackString<0>>()
            .parse_remaining::<u8>()
            .is_none())
    }

    #[test]
    fn parse_fail() {
        assert!(IterTokens::into_tokens("256".bytes())
            .as_buffered::<StackString<3>>()
            .parse_remaining::<u8>()
            .expect("NonEmpty")
            .is_err())
    }
}
