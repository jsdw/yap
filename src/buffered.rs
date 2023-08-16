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
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "123abc456".into_tokens();
    ///
    /// assert_eq!(tokens.as_buffered::<String>().parse_n::<u8>(3).expect("NonEmpty").expect("Parse success"), 123);
    /// ```
    pub fn parse_n<O>(&mut self, n: usize) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let to_parse = self.tokens.as_iter().take(n).collect::<Buf>();
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
    /// assert_eq!(tokens.as_buffered::<String>().parse_remaining::<u16>().expect("NonEmpty").expect("Parse success"), 65535);
    /// ```
    pub fn parse_remaining<O>(&mut self) -> Option<Result<O, <O as FromStr>::Err>>
    where
        O: FromStr,
    {
        let to_parse = self.tokens.as_iter().collect::<Buf>();
        (!to_parse.is_empty()).then(|| to_parse.parse::<O>())
    }

    /// Use [`str::parse`] to parse the next chunk of input matching a predicate.
    /// [`None`] if this is 0 elements.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered::<String>()
    ///         .parse_while::<u16, _>(|&t| t.to_digit(10).unwrap() < 6)
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     12345
    /// );
    /// ```
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
    /// Parse next chunk of digits.
    /// # Example
    /// ```
    /// use yap::{Tokens, IntoTokens};
    ///
    /// let mut tokens = "123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered::<String>()
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
    ///         .as_buffered::<String>()
    ///         .signed_digit::<i32>()
    ///         .expect("NonEmpty")
    ///         .expect("Parse success"),
    ///     123456
    /// );
    ///
    /// let mut tokens = "-123456".into_tokens();
    ///
    /// assert_eq!(tokens
    ///         .as_buffered::<String>()
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
    ///         .as_buffered::<String>()
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
    ///         .as_buffered::<String>()
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
        let a: String = IterTokens::into_tokens("123🗻∈🌏".chars())
            .as_buffered::<StackString<14>>()
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
            .as_buffered::<StackString<4>>()
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
