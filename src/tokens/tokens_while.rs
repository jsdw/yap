use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::tokens_while`].
#[derive(Debug)]
pub struct TokensWhile<'a, T, F> {
    tokens: &'a mut T,
    take_while: F,
}

impl<'a, T, F> TokensWhile<'a, T, F> {
    pub(crate) fn new(tokens: &'a mut T, take_while: F) -> Self {
        Self { tokens, take_while }
    }
}

impl<'a, T, F> Iterator for TokensWhile<'a, T, F>
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
