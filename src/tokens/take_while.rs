use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::take_while`].
#[derive(Debug)]
pub struct TakeWhile<'a, T, F> {
    tokens: &'a mut T,
    take_while: F,
}

impl<'a, T, F> TakeWhile<'a, T, F> {
    pub(crate) fn new(tokens: &'a mut T, take_while: F) -> Self {
        Self { tokens, take_while }
    }
}

impl<'a, T, F> Iterator for TakeWhile<'a, T, F>
where
    T: Tokens,
    F: FnMut(&T::Item) -> bool,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.tokens.location();
        match self.tokens.next() {
            Some(token) if (self.take_while)(&token) => Some(token),
            _ => {
                self.tokens.set_location(pos);
                None
            }
        }
    }
}

impl<'a, T, F> Tokens for TakeWhile<'a, T, F>
where
    T: Tokens,
    F: FnMut(&T::Item) -> bool,
{
    type Item = T::Item;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        Iterator::next(self)
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

    // Delegate to `parse_slice` here, since that function can be optimised
    // by specific implementations.
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        // Consume all of the tokens this TakeWhile wants:
        let start_loc = self.location();
        while Iterator::next(self).is_some() {}
        let end_loc = self.location();

        // Try parsing them:
        let res = self
            .tokens
            .parse_slice::<Out, Buf>(start_loc.clone(), end_loc);
        // Don't consume anything on error:
        if res.is_err() {
            self.set_location(start_loc);
        }
        res
    }
}
