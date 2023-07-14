//! This module contains types which implement the [`Tokens`] interface. You
//! won't often need to import this module unless you wish to explicitly name
//! the types in question.
//!
//! You should be able to remain generic by using `t: &mut impl Tokens<Item=char>` as a
//! function argument instead of naming concrete types like the ones here.
use super::{IntoTokens, TokenLocation, Tokens};

/// This is what we are given back if we call `into_tokens()` on
/// a `&[T]`. It implements the [`Tokens`] interface.
pub struct SliceTokens<'a, Item> {
    slice: &'a [Item],
    cursor: usize,
}

/// This implements [`TokenLocation`] and stores the location of
/// our current cursor into some slice.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct SliceTokensLocation(usize);

impl TokenLocation for SliceTokensLocation {
    fn offset(&self) -> usize {
        self.0
    }
}

impl<'a, Item> SliceTokens<'a, Item> {
    /// Return the parsed portion of the slice.
    pub fn consumed(&self) -> &'a [Item] {
        &self.slice[..self.cursor]
    }

    /// Return the unparsed remainder of the slice.
    pub fn remaining(&self) -> &'a [Item] {
        &self.slice[self.cursor..]
    }
}

impl<'a, Item> From<SliceTokens<'a, Item>> for &'a [Item] {
    fn from(toks: SliceTokens<'a, Item>) -> Self {
        toks.slice
    }
}

impl<'a, Item> Tokens for SliceTokens<'a, Item> {
    type Item = &'a Item;
    type Location = SliceTokensLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.slice.get(self.cursor);
        self.cursor += 1;
        res
    }
    fn location(&self) -> Self::Location {
        SliceTokensLocation(self.cursor)
    }
    fn set_location(&mut self, location: Self::Location) {
        self.cursor = location.0;
    }
    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.cursor == location.0
    }
}

impl<'a, Item> IntoTokens<&'a Item> for SliceTokens<'a, Item> {
    type Tokens = Self;
    fn into_tokens(self) -> Self {
        self
    }
}

impl<'a, Item> IntoTokens<&'a Item> for &'a [Item] {
    type Tokens = SliceTokens<'a, Item>;
    fn into_tokens(self) -> Self::Tokens {
        SliceTokens {
            slice: self,
            cursor: 0,
        }
    }
}

/// This is what we are given back if we call `into_tokens()` on
/// a `&str`. It implements the [`Tokens`] interface.
pub struct StrTokens<'a> {
    str: &'a str,
    cursor: usize,
}

/// This implements [`TokenLocation`] and stores the location of
/// our current cursor into some string. The location is the byte index
/// into the string and not the nth character we're up to (a character
/// may be represented by several bytes).
#[derive(Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd, Debug)]
pub struct StrTokensLocation(usize);

impl TokenLocation for StrTokensLocation {
    fn offset(&self) -> usize {
        self.0
    }
}

impl<'a> StrTokens<'a> {
    /// Return the parsed portion of the str.
    pub fn consumed(&self) -> &'a str {
        &self.str[..self.cursor]
    }

    /// Return the unparsed remainder of the str.
    pub fn remaining(&self) -> &'a str {
        &self.str[self.cursor..]
    }
}

impl<'a> From<StrTokens<'a>> for &'a str {
    fn from(toks: StrTokens<'a>) -> Self {
        toks.str
    }
}

impl<'a> Tokens for StrTokens<'a> {
    type Item = char;
    type Location = StrTokensLocation;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor == self.str.len() {
            return None;
        }

        // Cursor should always start at a valid char boundary.
        // So, we just find the next char boundary and return the
        // char between those two.
        let mut next_char_boundary = self.cursor + 1;
        while !self.str.is_char_boundary(next_char_boundary) {
            next_char_boundary += 1;
        }

        // We have to go to &str and then char. Unchecked because we know
        // that we are on a valid boundary. There's probably a quicker way..
        // To check that bounds detection works even on exotic characters, there's a test included
        // at the end of the file.
        let next_char = unsafe { self.str.get_unchecked(self.cursor..next_char_boundary) }
            .chars()
            .next()
            .unwrap();

        self.cursor = next_char_boundary;
        Some(next_char)
    }
    fn location(&self) -> Self::Location {
        StrTokensLocation(self.cursor)
    }
    fn set_location(&mut self, location: Self::Location) {
        self.cursor = location.0;
    }
    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.cursor == location.0
    }
}

impl<'a> IntoTokens<char> for StrTokens<'a> {
    type Tokens = Self;
    fn into_tokens(self) -> Self {
        self
    }
}

impl<'a> IntoTokens<char> for &'a str {
    type Tokens = StrTokens<'a>;
    fn into_tokens(self) -> Self::Tokens {
        StrTokens {
            str: self,
            cursor: 0,
        }
    }
}

/// This is what we are given back if we call [`IterTokens::into_tokens(iter)`] on
/// an `impl Iterator + Clone`. It implements the [`Tokens`] interface.
#[derive(Clone)]
pub struct IterTokens<I> {
    iter: I,
    cursor: usize,
}

/// This implements [`TokenLocation`] and stores the location and state of
/// our current cursor into some iterator. The location is equivalent to `offset`
/// in [`Iterator::nth(offset)`].
#[derive(Clone)]
pub struct IterTokensLocation<I>(IterTokens<I>);

impl<I> core::fmt::Debug for IterTokensLocation<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "IterTokensLocation(cursor = {})", self.0.cursor)
    }
}

// Locations match as long as the cursors do. This is as strong as the guarantee
// for string or slice locations, and in all cases, locations from StrTokens/SliceTokens
// may be equal even if the underlying tokens are different.
impl<I> PartialEq for IterTokensLocation<I> {
    fn eq(&self, other: &Self) -> bool {
        self.0.cursor == other.0.cursor
    }
}

impl<I> TokenLocation for IterTokensLocation<I> {
    fn offset(&self) -> usize {
        self.0.cursor
    }
}

impl<I: Iterator + Clone> IterTokens<I> {
    /// We can't define a blanket impl for [`IntoTokens`] on all `impl Iterator + Clone` without
    /// [specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html).
    ///
    /// Instead, use this method to convert a suitable iterator into [`Tokens`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, types::IterTokens };
    ///
    /// // In normal usage, "hello \n\t world".into_tokens()
    /// // would be preferred here (which would give StrTokens).
    /// // This is just to demonstrate using IterTokens:
    /// let chars_iter = "hello \n\t world".chars();
    /// let mut tokens = IterTokens::into_tokens(chars_iter);
    ///
    /// // now we have tokens, we can do some parsing:
    /// assert!(tokens.tokens("hello".chars()));
    /// tokens.skip_tokens_while(|c| c.is_whitespace());
    /// assert!(tokens.tokens("world".chars()));
    /// ```
    pub fn into_tokens(iter: I) -> Self {
        IterTokens { iter, cursor: 0 }
    }
}

impl<I> Tokens for IterTokens<I>
where
    I: Iterator + Clone,
{
    type Item = I::Item;
    type Location = IterTokensLocation<I>;

    fn next(&mut self) -> Option<Self::Item> {
        self.cursor += 1;
        self.iter.next()
    }
    fn location(&self) -> Self::Location {
        IterTokensLocation(self.clone())
    }
    fn set_location(&mut self, location: Self::Location) {
        *self = location.0;
    }
    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.cursor == location.0.cursor
    }
}

impl<I> IntoTokens<I::Item> for IterTokens<I>
where
    I: Iterator + Clone,
{
    type Tokens = Self;
    fn into_tokens(self) -> Self {
        self
    }
}

/// Embed some context with your [`Tokens`] implementation to
/// access at any time. Use [`Tokens::with_context`] to produce this.
pub struct WithContext<T, C> {
    tokens: T,
    context: C,
}

/// Embed some context with a mutable reference to your [`Tokens`] to
/// access at any time. Use [`Tokens::with_context`] to produce this.
pub struct WithContextMut<T, C> {
    tokens: T,
    context: C,
}

// `WithContext` and `WithContextMut` have almost identical looking impls,
// but one only works with `Tokens`, and one with `&mut Tokens` (because
// those impls would conflict if both on the same struct).
macro_rules! with_context_impls {
    ($name:ident $( $($mut:tt)+ )?) => {
        impl <T, C> $name<T, C> {
            /// Provide something that implements [`Tokens`] and
            /// some arbitrary context.
            pub(crate) fn new(tokens: T, context: C) -> Self {
                Self { tokens, context }
            }

            /// Return the original tokens and context
            pub fn into_parts(self) -> (T, C) {
                (self.tokens, self.context)
            }

            /// Access the context
            pub fn context(&self) -> &C {
                &self.context
            }

            /// Mutably access the context
            pub fn context_mut(&mut self) -> &mut C {
                &mut self.context
            }
        }

        impl <T, C> Tokens for $name<$( $($mut)+ )? T, C>
        where T: Tokens {
            type Item = T::Item;
            type Location = T::Location;

            fn next(&mut self) -> Option<Self::Item> {
                self.tokens.next()
            }
            fn location(&self) -> Self::Location {
                self.tokens.location()
            }
            fn set_location(&mut self, location: Self::Location) {
                self.tokens.set_location(location)
            }
            fn is_at_location(&self, location: &Self::Location) -> bool {
                self.tokens.is_at_location(location)
            }
        }
    }
}

with_context_impls!(WithContext);
with_context_impls!(WithContextMut &mut);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exotic_character_bounds() {
        let mut tokens = "🗻∈🌏".into_tokens();

        assert_eq!(tokens.next(), Some('🗻'));
        assert_eq!(tokens.next(), Some('∈'));
        assert_eq!(tokens.next(), Some('🌏'));
    }

    #[test]
    fn iterator_tokens_sanity_check() {
        // In reality, one should always prefer to use StrTokens for strings:
        let chars = "hello \n\t world".chars();
        let mut tokens = IterTokens::into_tokens(chars);

        let loc = tokens.location();
        assert!(tokens.tokens("hello".chars()));

        tokens.set_location(loc.clone());
        assert!(tokens.tokens("hello".chars()));

        tokens.skip_tokens_while(|c| c.is_whitespace());

        assert!(tokens.tokens("world".chars()));

        tokens.set_location(loc);
        assert!(tokens.tokens("hello".chars()));
    }
}
