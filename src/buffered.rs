//! Collecting tokens into temporary buffers.

use crate::Tokens;
use core::{
    array,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// This is returned from [`Tokens::as_buffered()`], and exposes methods
/// requiring temporary allocations on our tokens.
pub struct BufferedTokens<'a, T, Buf> {
    tokens: &'a mut T,
    buf: PhantomData<Buf>,
}

impl<'a, T, Buf> BufferedTokens<'a, T, Buf> {
    pub(crate) fn new(tokens: &'a mut T) -> Self {
        BufferedTokens {
            tokens,
            buf: core::marker::PhantomData,
        }
    }
}

impl<'a, T, Buf> BufferedTokens<'a, T, Buf>
where
    T: Tokens,
    Buf: FromIterator<T::Item> + Deref<Target = str>,
{
    /// This uses [`std::str::parse`] to parse the next `n` elements.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, buffered::StackString};
    ///
    /// let mut tokens = "123abc456def".into_tokens();
    /// let mut buffered = tokens.buffered::<StackString<3>>();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<u8>(3)
    ///         .expect("Parse success"),
    ///     123
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<String>(3)
    ///         .expect("Parse success"),
    ///     "abc"
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<u16>(3)
    ///         .expect("Parse success"),
    ///     456
    /// );
    /// assert_eq!(tokens.remaining(), "def");
    /// ```
    pub fn parse_n<O>(&mut self, n: usize) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        let buf = self.tokens.as_iter().take(n).collect::<Buf>();
        buf.parse::<O>()
    }

    /// This uses [`std::str::parse`] to parse the remaining elements
    /// until [`None`] is returned from the token iterator.
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
    ///         .buffered::<String>()
    ///         .parse_remaining::<u16>()
    ///         .expect("Parse success"),
    ///     65535
    /// );
    /// assert!(tokens.eof())
    /// ```
    pub fn parse_remaining<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        let buf = self.tokens.as_iter().collect::<Buf>();
        buf.parse::<O>()
    }

    /// This uses [`str::parse`] to parse the next chunk of input that matches
    /// the given predicate.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{buffered::StackString, IntoTokens, Tokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    /// let mut buffered = tokens.buffered::<StackString<5>>();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .parse_while::<u16, _>(|&t| t.to_digit(10).unwrap() < 6)
    ///         .expect("Parse success"),
    ///     12345
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_while::<u8, _>(|&t| t.to_digit(10).unwrap() == 6)
    ///         .expect("Parse success"),
    ///     6
    /// );
    /// ```
    pub fn parse_while<O, F>(&mut self, take_while: F) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
        F: FnMut(&T::Item) -> bool,
    {
        let buf = self.tokens.tokens_while(take_while).collect::<Buf>();
        buf.parse::<O>()
    }
}

impl<'a, T, Buf> BufferedTokens<'a, T, Buf>
where
    T: Tokens<Item = char>,
    Buf: FromIterator<T::Item> + Deref<Target = str>,
{
    /// Parse the next chunk of digits into the given type.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .buffered::<String>()
    ///         .digits::<u32>()
    ///         .expect("Parse success"),
    ///     123456
    /// );
    /// ```
    pub fn digits<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_numeric())
    }

    /// Parses the next chunk of digits with a sign (`+`/`-`) in front
    /// into the given type.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "+123456abc".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .buffered::<String>()
    ///         .signed_digits::<i32>()
    ///         .expect("Parse success"),
    ///     123456
    /// );
    /// assert_eq!(tokens.remaining(), "abc");
    ///
    /// let mut tokens = "-123456abc".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .buffered::<String>()
    ///         .signed_digits::<i32>()
    ///         .expect("Parse success"),
    ///     -123456
    /// );
    /// assert_eq!(tokens.remaining(), "abc");
    /// ```
    pub fn signed_digits<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        let mut first_char_seen = false;
        self.parse_while(|t| {
            let keep_tok = if first_char_seen {
                t.is_numeric()
            } else {
                t == &'-' || t == &'+'
            };
            first_char_seen = true;
            keep_tok
        })
    }

    /// Parses next chunk of alphabetical characters.
    ///
    /// # Example
    ///
    /// ```
    /// use core::str::FromStr;
    /// use yap::{Tokens, IntoTokens};
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct AB {
    ///     a: usize,
    ///     b: usize,
    /// }
    ///
    /// impl FromStr for AB {
    ///     type Err = ();
    ///
    ///     fn from_str(s: &str) -> Result<Self, Self::Err> {
    ///         let mut a = 0;
    ///         let mut b = 0;
    ///         for c in s.chars() {
    ///             match c {
    ///                 'a' => a += 1,
    ///                 'b' => b += 1,
    ///                 _ => return Err(()),
    ///             }
    ///         }
    ///         Ok(AB { a, b })
    ///     }
    /// }
    ///
    /// let mut tokens = "aaabb123".into_tokens();
    /// assert_eq!(
    ///     tokens
    ///         .buffered::<String>()
    ///         .alphabetic::<AB>()
    ///         .expect("Parse success"),
    ///     AB { a: 3, b: 2 }
    /// );
    /// assert_eq!(tokens.remaining(), "123");
    /// ```
    pub fn alphabetic<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_alphabetic())
    }

    /// Parses next chunk of alphanumeric characters.
    ///
    /// # Example
    ///
    /// ```
    /// use core::str::FromStr;
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "aab123".into_tokens();
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct ABNum {
    ///     a: usize,
    ///     b: usize,
    ///     num: u32,
    /// }
    ///
    /// impl FromStr for ABNum {
    ///     type Err = ();
    ///
    ///     fn from_str(s: &str) -> Result<Self, Self::Err> {
    ///         let mut a = 0;
    ///         let mut b = 0;
    ///         let mut num = 0;
    ///         for c in s.chars() {
    ///             match c {
    ///                 'a' => a += 1,
    ///                 'b' => b += 1,
    ///                 c if c.is_digit(10) => num += c.to_digit(10).unwrap(),
    ///                 _ => return Err(()),
    ///             }
    ///         }
    ///         Ok(ABNum { a, b, num })
    ///     }
    /// }
    ///
    /// assert_eq!(
    ///     tokens
    ///         .buffered::<String>()
    ///         .alphanumeric::<ABNum>()
    ///         .expect("Parse success"),
    ///     ABNum { a: 2, b: 1, num: 6 }
    /// );
    /// ```
    pub fn alphanumeric<O>(&mut self) -> Result<O, <O as FromStr>::Err>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_alphanumeric())
    }
}

/// A type that can collect [`char`]s on the stack and is compatible with
/// [`yap::Tokens::buffered()`].
///
/// # Panics
///
/// Using `FromIter` to collect more chars than will fit in the buffer will
/// panic. `FromIter` is called implicitly in many of the methods on [`BufferedTokens`].
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
    fn parse_remaining() {
        let s: String = "123🗻∈🌏"
            .into_tokens()
            .buffered::<String>()
            .parse_remaining()
            .expect("Parse success");
        assert_eq!(s, "123🗻∈🌏");

        let s: String = IterTokens::new("123🗻∈🌏".chars())
            .buffered::<StackString<14>>()
            .parse_remaining()
            .expect("Parse success");
        assert_eq!(s, "123🗻∈🌏");
    }

    #[test]
    fn parse_remaining_fails_number_out_of_range() {
        assert!(IterTokens::new("256".chars())
            .buffered::<StackString<3>>()
            .parse_remaining::<u8>()
            .is_err())
    }

    #[test]
    fn parse_digits() {
        let a: u8 = "123🗻∈🌏"
            .into_tokens()
            .buffered::<String>()
            .digits()
            .expect("Parse success");
        assert_eq!(a, 123);
    }

    #[test]
    fn parse_signed_digits() {
        let a: i8 = "-123"
            .into_tokens()
            .buffered::<StackString<4>>()
            .signed_digits()
            .expect("Parse success");
        assert_eq!(a, -123);
    }

    #[test]
    fn parse_n() {
        let a: i32 = IterTokens::new("-123456789🗻∈🌏".chars())
            .buffered::<StackString<10>>()
            .parse_n(10)
            .expect("Parse success");
        assert_eq!(a, -123456789);
        let a: i32 = IterTokens::new("-123456789🗻∈🌏".chars())
            .buffered::<StackString<20>>()
            .parse_n(10)
            .expect("Parse success");
        assert_eq!(a, -123456789);
    }
}
