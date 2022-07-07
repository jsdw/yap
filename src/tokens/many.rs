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

impl<'a, T, F, Output> Iterator for Many<'a, T, F>
where
    T: Tokens,
    F: FnMut(&mut T) -> Option<Output>,
{
    type Item = Output;

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
}
