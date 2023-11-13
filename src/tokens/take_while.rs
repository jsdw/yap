use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::take_while`].
#[derive(Debug)]
pub struct TakeWhile<'a, T, F> {
    tokens: &'a mut T,
    take_while: F,
    done: bool,
}

impl<'a, T, F> TakeWhile<'a, T, F> {
    pub(crate) fn new(tokens: &'a mut T, take_while: F) -> Self {
        Self {
            tokens,
            take_while,
            done: false,
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
        if self.done {
            return None;
        }

        let pos = self.tokens.location();
        match self.tokens.next() {
            Some(token) if (self.take_while)(&token) => Some(token),
            _ => {
                self.done = true;
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

    // Delegate to root Tokens impl to allow optimisation.
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        let res = self
            .tokens
            .parse_take_while::<Out, Buf, _>(&mut self.take_while);
        // Assume that underlying token location has been updated properly,
        // but we still need to update our state here accordingly:
        if res.is_ok() {
            self.done = true;
        }
        res
    }
}

#[cfg(test)]
mod test {
    use crate::{IntoTokens, Tokens};

    #[test]
    fn test_parse_success() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take_while(|t| t.is_numeric());

        let n = tw.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(tw.as_iter().collect::<String>(), "");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take_while(|t| t.is_numeric());

        tw.parse::<u8, String>().unwrap_err();
        assert_eq!(tw.as_iter().collect::<String>(), "345");
    }
}
