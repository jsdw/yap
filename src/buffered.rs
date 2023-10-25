//! Manipulating tokens with in-memory buffers.

use crate::Tokens;
use core::{
    array,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// This is returned from [`Tokens::as_buffered()`], and exposes methods
/// requiring in-memory buffers of our tokens.
pub struct BufferedTokens<'a, T> {
    pub(crate) tokens: &'a mut T,
}

impl<'a, T> BufferedTokens<'a, T>
where
    T: Tokens,
    for<'buf> T::Buffer<'buf>: Deref<Target = str>,
{
    /// Use [`str::parse`] to parse the next `n` elements.
    /// [`None`] if this is 0 elements.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens, buffered::StackString};
    ///
    /// let mut tokens = "123abc456".into_tokens();
    /// let mut buffered = tokens.as_buffered();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<u8>(3)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     123
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<String>(3)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     "abc"
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_n::<u16>(3)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     456
    /// );
    /// ```
    pub fn parse_n<O>(&mut self, n: usize) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let start = self.tokens.location();
        self.tokens.as_iter().take(n).for_each(drop);
        let end = self.tokens.location();
        let to_parse = self.tokens.get_buffer(start, end);
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }

    /// Use [`str::parse`] to parse the remaining elements until the next [`None`].
    /// [`None`] if this is 0 elements.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "65535".into_tokens();
    ///
    /// assert_eq!(
    ///     tokens
    ///         .as_buffered()
    ///         .parse_remaining::<u16>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     65535
    /// );
    /// assert!(tokens.eof())
    /// ```
    pub fn parse_remaining<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let start = self.tokens.location();
        self.tokens.as_iter().for_each(drop);
        let end = self.tokens.location();
        let to_parse = self.tokens.get_buffer(start, end);
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }

    /// Use [`str::parse`] to parse the next chunk of input matching a predicate.
    /// [`None`] if this is 0 elements.
    /// # Example
    /// ```
    /// use yap::{IntoTokens, Tokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    /// let mut buffered = tokens.as_buffered();
    ///
    /// assert_eq!(
    ///     buffered
    ///         .parse_while::<u16, _>(|&t| t.to_digit(10).unwrap() < 6)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     12345
    /// );
    /// assert_eq!(
    ///     buffered
    ///         .parse_while::<u8, _>(|&t| t.to_digit(10).unwrap() == 6)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     6
    /// );
    /// ```
    pub fn parse_while<O, F>(&mut self, take_while: F) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
        F: FnMut(&T::Item) -> bool,
    {
        let start = self.tokens.location();
        self.tokens.tokens_while(take_while).for_each(drop);
        let end = self.tokens.location();
        let to_parse = self.tokens.get_buffer(start, end);
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }
}

impl<'a, T> BufferedTokens<'a, T>
where
    T: Tokens<Item = char>,
    for<'buf> T::Buffer<'buf>: Deref<Target = str>,
{
    /// Parse next chunk of digits.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered()
    ///         .digit::<u32>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     123456
    /// );
    /// ```
    pub fn digit<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_numeric())
    }

    /// Parses next chunk of digits with a sign (`+`/`-`) in front.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "+123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered()
    ///         .signed_digit::<i32>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     123456
    /// );
    ///
    /// let mut tokens = "-123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered()
    ///         .signed_digit::<i32>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     -123456
    /// );
    /// ```
    pub fn signed_digit<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let start = self.tokens.location();
        let sign = self.tokens.next()?;
        match sign {
            '+' | '-' => {
                self.tokens.tokens_while(|&t| t.is_numeric()).for_each(drop);
                let end = self.tokens.location();
                let to_parse = self.tokens.get_buffer(start, end);
                (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
            }
            _ => {
                self.tokens.set_location(start);
                None
            }
        }
    }

    /// Parses next chunk of alphabetical characters.
    /// # Example
    /// ```
    /// use core::str::FromStr;
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "aab123".into_tokens();
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
    /// assert_eq!(
    ///     tokens
    ///         .as_buffered()
    ///         .alpha::<AB>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     AB { a: 2, b: 1 }
    /// );
    /// ```
    pub fn alpha<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        self.parse_while(|t| t.is_alphabetic())
    }

    /// Parses next chunk of alphanumeric characters.
    /// # Example
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
    ///         .as_buffered()
    ///         .alphanumeric::<ABNum>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     ABNum { a: 2, b: 1, num: 6 }
    /// );
    /// ```
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
/// - Collecting more [`u8`] than the buffer's max size causes a panic.
/// - Invalid-Utf8 will panic when dereferencing to a [`str`].
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StackString<const N: usize> {
    buf: [u8; N],
    len: usize,
}

impl<const N: usize> StackString<N> {
    /// Push a new [`u8`] onto the [`StackString`]. Failing if not enough room.
    /// It is ok to make the [`StackString`] invalid Utf8 as long as
    /// it is not dereferenced as a [`str`] while invalid.
    #[allow(clippy::result_unit_err)]
    pub fn push(&mut self, val: u8) -> Result<(), ()> {
        if self.len == N {
            return Err(());
        }
        self.buf[self.len] = val;
        self.len += 1;
        Ok(())
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

impl<const N: usize> FromIterator<u8> for StackString<N> {
    /// Creates a [`StackString`] from an iterator.
    /// # Panics
    /// Panics if the iterator is longer than the internal buffer of the [`StackString`]
    fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
        let mut out = Self::default();
        for (i, val) in iter.into_iter().enumerate() {
            assert!(i < N, "Iterator longer than max buffer length ({N})");
            out.buf[i] = val;
            out.len += 1;
        }
        out
    }
}

impl<const N: usize> FromIterator<char> for StackString<N> {
    /// Creates a [`StackString`] from an iterator.
    /// # Panics
    /// Panics if the iterator is longer than the internal buffer of the [`StackString`]
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut out = Self::default();
        for val in iter.into_iter() {
            let mut buf = [0; 4];
            let encoded = val.encode_utf8(&mut buf);
            let remaining = N - out.len;
            if remaining >= encoded.len() {
                for b in encoded.bytes() {
                    out.push(b).expect("Enough capacity left")
                }
            } else {
                panic!("Iterator longer than max buffer length ({N})");
            }
        }
        out
    }
}

impl<const N: usize> FromStr for StackString<N> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut out = StackString::default();
        // FromIterator impl panics. Use this instead.
        for b in s.bytes() {
            out.push(b)?
        }
        Ok(out)
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
            .as_buffered()
            .parse_remaining()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, "123🗻∈🌏");
        let a: String = IterTokens::<_, String>::into_tokens("123🗻∈🌏".chars())
            .as_buffered()
            .parse_remaining()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, "123🗻∈🌏");
    }

    #[test]
    fn parse_unsigned() {
        let a: u8 = ("123🗻∈🌏".into_tokens())
            .as_buffered()
            .digit()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 123);
    }

    #[test]
    fn parse_signed() {
        let a: u8 = "+123"
            .into_tokens()
            .as_buffered()
            .parse_n(3)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 12);
        let a: i8 = "+123"
            .into_tokens()
            .as_buffered()
            .parse_n(3)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, 12);
        let a: i8 = "-123"
            .into_tokens()
            .as_buffered()
            .signed_digit()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123);
    }

    #[test]
    fn parse_stack() {
        let a: i32 = IterTokens::<_, StackString<10>>::into_tokens("-123456789🗻∈🌏".bytes())
            .as_buffered()
            .parse_n(10)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123456789);
        let a: i32 = IterTokens::<_, StackString<20>>::into_tokens("-123456789🗻∈🌏".bytes())
            .as_buffered()
            .parse_n(10)
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(a, -123456789);
        let a: StackString<21> = "-123456789🗻∈🌏"
            .into_tokens()
            .as_buffered()
            .parse_remaining()
            .expect("NonEmpty")
            .expect("Parse success");
        assert_eq!(&*a, "-123456789🗻∈🌏");
    }

    #[test]
    fn parse_empty() {
        assert!(IterTokens::<_, StackString<0>>::into_tokens("".bytes())
            .as_buffered()
            .parse_remaining::<u8>()
            .is_none())
    }

    #[test]
    fn parse_fail() {
        assert!(IterTokens::<_, StackString<3>>::into_tokens("256".bytes())
            .as_buffered()
            .parse_remaining::<u8>()
            .expect("NonEmpty")
            .is_err())
    }
}
