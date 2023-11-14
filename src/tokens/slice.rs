use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::slice`].
pub struct Slice<'a, T: Tokens> {
    tokens: &'a mut T,
    original: T::Location,
    from: T::Location,
    to: T::Location,
}

impl<'a, T: Tokens> Slice<'a, T> {
    pub(crate) fn new(
        tokens: &'a mut T,
        current: T::Location,
        from: T::Location,
        to: T::Location,
    ) -> Slice<'a, T> {
        // shift tokens to the start location. Dropping
        // this will reset them back to the original one.
        tokens.set_location(from.clone());
        Slice {
            tokens,
            from,
            original: current,
            to,
        }
    }
}

// We can also treat this slice of tokens as tokens, too:
impl<'a, T: Tokens> Tokens for Slice<'a, T> {
    type Item = T::Item;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        if self.tokens.is_at_location(&self.to) {
            None
        } else {
            self.tokens.next()
        }
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

    // Allow toks.slice(..).parse(..) to be optimised.
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        let res = self
            .tokens
            .parse_slice::<Out, Buf>(self.from.clone(), self.to.clone());
        // If the underlying parse worked, then "consume" the slice in case
        // we try using it again. If it didn't work then leave as is.
        if res.is_ok() {
            self.set_location(self.to.clone());
        }
        res
    }
}

impl<'a, T: Tokens> Drop for Slice<'a, T> {
    fn drop(&mut self) {
        // Reset the location on drop so that the tokens
        // remain unaffected by this iterator:
        self.tokens.set_location(self.original.clone());
    }
}

#[cfg(test)]
mod test {
    use crate::{IntoTokens, Tokens};

    #[test]
    fn test_parse_success() {
        let mut toks = "345abc".into_tokens();

        // get locations for testing:
        let from = toks.location();
        toks.take_while(|t| t.is_numeric()).consume();
        let to = toks.location();

        // Advance 1 beyond the slice end:
        toks.take(1).consume();

        let mut s = toks.slice(from, to);
        let n = s.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(s.collect::<String>(), "");

        // We should be where we were originally (1 after slice)
        drop(s);
        assert_eq!(toks.collect::<String>(), "bc");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        // get locations for testing:
        let from = toks.location();
        toks.take_while(|t| t.is_numeric()).consume();
        let to = toks.location();

        // Advance 1 beyond the slice end:
        toks.take(1).consume();

        // Try the slice:
        let mut s = toks.slice(from, to);
        s.parse::<u8, String>().unwrap_err();
        assert_eq!(s.collect::<String>(), "345");

        // We should be where we were originally (1 after slice)
        drop(s);
        assert_eq!(toks.collect::<String>(), "bc");
    }
}
