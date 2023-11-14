use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::many`].
#[derive(Debug)]
pub struct Many<'a, T, F> {
    tokens: &'a mut T,
    parser: F,
}

impl<'a, T, F> Many<'a, T, F> {
    pub(crate) fn new(tokens: &'a mut T, parser: F) -> Self {
        Self { tokens, parser }
    }
}

impl<'a, T, F, Output> Tokens for Many<'a, T, F>
where
    T: Tokens,
    F: FnMut(&mut T) -> Option<Output>,
{
    type Item = Output;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        let pos = self.tokens.location();
        match (self.parser)(self.tokens) {
            Some(output) => Some(output),
            None => {
                self.tokens.set_location(pos);
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
