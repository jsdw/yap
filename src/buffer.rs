//! Buffer types for collecting tokens into.

use core::{
    array,
    ops::{Deref, DerefMut},
    str::FromStr,
};

/// A type that can collect [`char`]s on the stack and can be used in conjunction
/// with [`crate::Tokens::parse()`].
///
/// # Panics
///
/// Using `FromIter` to collect more chars than will fit in the buffer will
/// panic. `FromIter` is called implicitly as a result of calling
/// [`crate::Tokens::parse()`].
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

    #[test]
    fn stack_string_from_iter() {
        assert_eq!(
            StackString::<20>::from_iter("123🗻∈🌏".chars()).to_string(),
            "123🗻∈🌏"
        );
    }
}
