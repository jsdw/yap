use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::sep_by_all_err`].
#[derive(Debug)]
pub struct SepByAllErr<'a, T: Tokens, F, S, Output> {
    tokens: &'a mut T,
    parser: F,
    separator: S,
    next_output: Option<(Output, T::Location)>,
    needs_separator: bool,
    finished: bool,
}

impl<'a, T: Tokens, F, S, Output> SepByAllErr<'a, T, F, S, Output> {
    pub(crate) fn new(tokens: &'a mut T, parser: F, separator: S) -> Self {
        Self {
            tokens,
            parser,
            separator,
            next_output: None,
            needs_separator: false,
            finished: false,
        }
    }
}

impl<'a, T, F, S, Output, E> Tokens for SepByAllErr<'a, T, F, S, Output>
where
    T: Tokens,
    F: FnMut(&mut T) -> Result<Output, E>,
    S: FnMut(&mut T) -> Option<Output>,
{
    type Item = Result<Output, E>;
    type Location = T::Location;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let last_good_pos = self.tokens.location();

        // Parse the first input:
        if !self.needs_separator {
            return match (self.parser)(self.tokens) {
                Ok(output) => {
                    self.needs_separator = true;
                    Some(Ok(output))
                }
                Err(e) => {
                    self.tokens.set_location(last_good_pos);
                    self.finished = true;
                    Some(Err(e))
                }
            };
        }

        // If we've already parsed the next output, return that,
        // moving location to after the output for the next iteration.
        if let Some((output, loc)) = self.next_output.take() {
            self.tokens.set_location(loc);
            return Some(Ok(output));
        }

        // Parse the separator and then the next output (to make sure
        // that the separator is valid before returning it). Store the
        // next output to return next iteration, and return separator this one.
        let sep = match (self.separator)(self.tokens) {
            Some(sep) => sep,
            None => {
                self.tokens.set_location(last_good_pos);
                self.finished = true;
                return None;
            }
        };
        match (self.parser)(self.tokens) {
            Ok(output) => {
                let loc = self.tokens.location();
                self.next_output = Some((output, loc));
            }
            Err(e) => {
                self.tokens.set_location(last_good_pos);
                self.finished = true;
                return Some(Err(e));
            }
        };
        Some(Ok(sep))
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
