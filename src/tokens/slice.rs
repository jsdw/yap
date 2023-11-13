use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::slice`].
pub struct Slice<'a, T: Tokens> {
    tokens: &'a mut T,
    original: T::Location,
    started: bool,
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
        Slice {
            tokens,
            original: current,
            from,
            to,
            started: false,
        }
    }
}

// We can also treat this slice of tokens as tokens, too:
impl<'a, T: Tokens> Tokens for Slice<'a, T> {
    type Item = T::Item;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        // Initial prep:
        if !self.started {
            self.tokens.set_location(self.from.clone());
            self.started = true;
        }

        // Once we hit the "to" location we return None
        // (this isn't an inclusive iterator).
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

    // Delegate to root Tokens impl to allow optimisation.
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
            self.from = self.to.clone();
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
        toks.take_while(|t| t.is_numeric()).as_iter().for_each(drop);
        let to = toks.location();

        let mut s = toks.slice(from, to);

        let n = s.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(s.as_iter().collect::<String>(), "");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        // get locations for testing:
        let from = toks.location();
        toks.take_while(|t| t.is_numeric()).as_iter().for_each(drop);
        let to = toks.location();

        let mut s = toks.slice(from, to);

        s.parse::<u8, String>().unwrap_err();
        assert_eq!(s.as_iter().collect::<String>(), "345");
    }
}
