use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::many_err`].
#[derive(Debug)]
pub struct ManyErr<'a, T, F> {
    tokens: &'a mut T,
    parser: F,
    finished: bool,
}

impl<'a, T, F> ManyErr<'a, T, F> {
    pub(crate) fn new(tokens: &'a mut T, parser: F) -> Self {
        Self {
            tokens,
            parser,
            finished: false,
        }
    }
}

impl<'a, T, F, E, Output> Tokens for ManyErr<'a, T, F>
where
    T: Tokens,
    F: FnMut(&mut T) -> Result<Output, E>,
{
    type Item = Result<Output, E>;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let pos = self.tokens.location();
        match (self.parser)(self.tokens) {
            Ok(output) => Some(Ok(output)),
            Err(e) => {
                self.tokens.set_location(pos);
                // Stop after error:
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
