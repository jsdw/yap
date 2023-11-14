use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::sep_by`].
#[derive(Debug)]
pub struct SepBy<'a, T, F, S> {
    tokens: &'a mut T,
    parser: F,
    separator: S,
    needs_separator: bool,
}

impl<'a, T, F, S> SepBy<'a, T, F, S> {
    pub(crate) fn new(tokens: &'a mut T, parser: F, separator: S) -> Self {
        Self {
            tokens,
            parser,
            separator,
            needs_separator: false,
        }
    }
}

impl<'a, T, F, S, Output> Tokens for SepBy<'a, T, F, S>
where
    T: Tokens,
    F: FnMut(&mut T) -> Option<Output>,
    S: FnMut(&mut T) -> bool,
{
    type Item = Output;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        let last_good_pos = self.tokens.location();

        if self.needs_separator && !(self.separator)(self.tokens) {
            // no separator found, but we needed one!
            self.tokens.set_location(last_good_pos);
            return None;
        }

        match (self.parser)(self.tokens) {
            Some(output) => {
                self.needs_separator = true;
                Some(output)
            }
            None => {
                // rewind to before separator was parsed; no more items.
                self.tokens.set_location(last_good_pos);
                None
            }
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
}
