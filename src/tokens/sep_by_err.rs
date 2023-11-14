use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::sep_by_err`].
#[derive(Debug)]
pub struct SepByErr<'a, T, F, S> {
    tokens: &'a mut T,
    parser: F,
    separator: S,
    needs_separator: bool,
    finished: bool,
}

impl<'a, T, F, S> SepByErr<'a, T, F, S> {
    pub(crate) fn new(tokens: &'a mut T, parser: F, separator: S) -> Self {
        Self {
            tokens,
            parser,
            separator,
            needs_separator: false,
            finished: false,
        }
    }
}

impl<'a, T, F, S, Output, E> Tokens for SepByErr<'a, T, F, S>
where
    T: Tokens,
    F: FnMut(&mut T) -> Result<Output, E>,
    S: FnMut(&mut T) -> bool,
{
    type Item = Result<Output, E>;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let last_good_pos = self.tokens.location();

        if self.needs_separator && !(self.separator)(self.tokens) {
            // no separator found, but we needed one!
            self.tokens.set_location(last_good_pos);
            return None;
        }

        match (self.parser)(self.tokens) {
            Ok(output) => {
                self.needs_separator = true;
                Some(Ok(output))
            }
            Err(e) => {
                // rewind to before separator was parsed; no more items.
                self.tokens.set_location(last_good_pos);
                // Once we hit an error, we're done iterating.
                self.finished = true;
                Some(Err(e))
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
