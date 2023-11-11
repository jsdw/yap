//! Collecting tokens into temporary buffers.

use crate::Tokens;
use core::{
    array,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// This is returned from [`Tokens::parse()`], and exposes methods
/// requiring temporary allocations on our tokens.
pub struct Parse<'a, T, Buf> {
    tokens: &'a mut T,
    buf: PhantomData<Buf>,
}

impl<'a, T, Buf> Parse<'a, T, Buf> {
    pub(crate) fn new(tokens: &'a mut T) -> Self {
        Parse {
            tokens,
            buf: core::marker::PhantomData,
        }
    }
}

impl<'a, T, Buf> Parse<'a, T, Buf>
where
    T: Tokens,
    Buf: FromIterator<T::Item> + Deref<Target = str>,
{
    /// This uses [`str::parse()`] to parse the next `n` elements.
    /// No tokens are consumed if the parsing fails.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, parse::StackString};
    ///
    /// let mut tokens = "123abc456def".into_tokens();
    /// let mut buffered = tokens.parse::<StackString<3>>();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .from_n::<u8>(3)
    ///         .expect("Parse success"),
    ///     123
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .from_n::<String>(3)
    ///         .expect("Parse success"),
    ///     "abc"
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .from_n::<u16>(3)
    ///         .expect("Parse success"),
    ///     456
    /// );
    /// assert_eq!(tokens.remaining(), "def");
    /// ```
    pub fn from_n<O>(&mut self, n: usize) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        self.tokens.optional_err(|tokens| {
            let buf = tokens.as_iter().take(n).collect::<Buf>();
            buf.parse::<O>()
        })
    }

    /// This uses [`str::parse`] to parse the remaining elements
    /// until [`None`] is returned from the token iterator. No tokens
    /// are consumed if the parsing fails.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "65535".into_tokens();
    ///
    /// assert_eq!(
    ///     tokens
    ///         .parse::<String>()
    ///         .from_remaining::<u16>()
    ///         .expect("Parse success"),
    ///     65535
    /// );
    /// assert!(tokens.eof())
    /// ```
    pub fn from_remaining<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        self.tokens.optional_err(|tokens| {
            let buf = tokens.as_iter().collect::<Buf>();
            buf.parse::<O>()
        })
    }

    /// This uses [`str::parse`] to parse the next chunk of input that matches
    /// the given predicate. No tokens are consumed if the parsing fails.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{parse::StackString, IntoTokens, Tokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    /// let mut buffered = tokens.parse::<StackString<5>>();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .from_filtered::<u16, _>(|&t| t.to_digit(10).unwrap() < 6)
    ///         .expect("Parse success"),
    ///     12345
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .from_filtered::<u8, _>(|&t| t.to_digit(10).unwrap() == 6)
    ///         .expect("Parse success"),
    ///     6
    /// );
    /// ```
    pub fn from_filtered<O, F>(&mut self, take_while: F) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
        F: FnMut(&T::Item) -> bool,
    {
        self.tokens.optional_err(move |tokens| {
            let buf = tokens.tokens_while(take_while).collect::<Buf>();
            buf.parse::<O>()
        })
    }
}

/// A type that can collect [`char`]s on the stack and can be used in conjunction
/// with [`crate::Tokens::parse()`].
///
/// # Panics
///
/// Using `FromIter` to collect more chars than will fit in the buffer will
/// panic. `FromIter` is called implicitly in many of the methods on [`Parse`].
///
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StackString<const N: usize> {
    buf: [u8; N],
    len: usize,
}

impl<const N: usize> StackString<N> {
    /// Attempt to push a new [`char`] onto the [`StackString`].
    /// Returns false if there is no more space.
    pub fn push(&mut self, val: char) -> bool {
        let mut buf = [0; 4];
        let encoded = val.encode_utf8(&mut buf);

        let remaining = N - self.len;
        if remaining < encoded.len() {
            return false;
        }

        for b in encoded.bytes() {
            self.buf[self.len] = b;
            self.len += 1;
        }
        true
    }
}

impl<const N: usize> Default for StackString<N> {
    fn default() -> Self {
        Self {
            buf: array::from_fn(|_| Default::default()),
            len: Default::default(),
        }
    }
}

impl<const N: usize> FromIterator<char> for StackString<N> {
    /// Creates a [`StackString`] from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the iterator is longer than the internal buffer of the [`StackString`].
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut out = Self::default();
        for char in iter.into_iter() {
            if !out.push(char) {
                panic!("Iterator longer than max buffer length ({N})");
            }
        }
        out
    }
}

impl<const N: usize> FromStr for StackString<N> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // String is too big to fit; error.
        if s.len() > N {
            return Err(());
        }

        // String will fit; manually copy bytes into the array:
        let mut out = StackString::default();
        out.buf[..s.len()].copy_from_slice(s.as_bytes());
        out.len = s.len();

        Ok(out)
    }
}

impl<const N: usize> Deref for StackString<N> {
    type Target = str;

    /// Dereferences the stack string to a `&str`.
    fn deref(&self) -> &Self::Target {
        core::str::from_utf8(&self.buf[..self.len]).expect("Valid Utf8")
    }
}

impl<const N: usize> DerefMut for StackString<N> {
    /// Dereferences the stack string to a `&mut str`.
    fn deref_mut(&mut self) -> &mut Self::Target {
        core::str::from_utf8_mut(&mut self.buf[..self.len]).expect("Valid Utf8")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{types::IterTokens, IntoTokens};

    #[test]
    fn stack_string_from_iter() {
        assert_eq!(
            StackString::<20>::from_iter("123🗻∈🌏".chars()).to_string(),
            "123🗻∈🌏"
        );
    }

    #[test]
    fn from_remaining() {
        let s: String = "123🗻∈🌏"
            .into_tokens()
            .parse::<String>()
            .from_remaining()
            .expect("Parse success");
        assert_eq!(s, "123🗻∈🌏");

        let s: String = IterTokens::new("123🗻∈🌏".chars())
            .parse::<StackString<14>>()
            .from_remaining()
            .expect("Parse success");
        assert_eq!(s, "123🗻∈🌏");
    }

    #[test]
    fn from_remaining_fails_number_out_of_range() {
        assert!(IterTokens::new("256".chars())
            .parse::<StackString<3>>()
            .from_remaining::<u8>()
            .is_err())
    }

    #[test]
    fn from_n() {
        let a: i32 = IterTokens::new("-123456789🗻∈🌏".chars())
            .parse::<StackString<10>>()
            .from_n(10)
            .expect("Parse success");
        assert_eq!(a, -123456789);
        let a: i32 = IterTokens::new("-123456789🗻∈🌏".chars())
            .parse::<StackString<20>>()
            .from_n(10)
            .expect("Parse success");
        assert_eq!(a, -123456789);
    }

    #[test]
    fn from_filtered_doesnt_consume_if_err() {
        let mut s = "256abc".into_tokens();
        assert!(s
            .parse::<String>()
            .from_filtered::<u8, _>(|t| t.is_numeric())
            .is_err());
        assert_eq!(s.offset(), 0);
    }

    #[test]
    fn from_n_doesnt_consume_if_err() {
        let mut s = "256abc".into_tokens();
        assert!(s.parse::<String>().from_n::<u8>(3).is_err());
        assert_eq!(s.offset(), 0);
    }

    #[test]
    fn from_remaining_doesnt_consume_if_err() {
        let mut s = "256".into_tokens();
        assert!(s.parse::<String>().from_remaining::<u8>().is_err());
        assert_eq!(s.offset(), 0);
    }
}
