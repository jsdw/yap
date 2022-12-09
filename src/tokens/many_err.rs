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

impl<'a, T, F, E, Output> Iterator for ManyErr<'a, T, F>
where
    T: Tokens,
    F: FnMut(&mut T) -> Result<Output, E>,
{
    type Item = Result<Output, E>;

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
}
