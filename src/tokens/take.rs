use crate::Tokens;

/// Produced by running [`crate::tokens::Tokens::take`].
#[derive(Debug)]
pub struct Take<'a, T> {
    tokens: &'a mut T,
    n: usize,
}

impl<'a, T> Take<'a, T> {
    pub(crate) fn new(tokens: &'a mut T, n: usize) -> Self {
        Self { tokens, n }
    }
}

impl<'a, T> Iterator for Take<'a, T>
where
    T: Tokens,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n == 0 {
            return None;
        }

        self.n -= 1;
        // This could return None, and we'd still
        // call it n more times if one really wanted
        // to continue calling this after None comes
        // back.
        self.tokens.next()
    }
}

impl<'a, T> Tokens for Take<'a, T>
where
    T: Tokens,
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

    // Delegate to root Tokens impl to allow optimisation.
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        let res = self.tokens.parse_take::<Out, Buf>(self.n);
        // Assume that underlying token location has been updated properly,
        // but we still need to update our state here accordingly:
        if res.is_ok() {
            self.n = 0;
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

        let mut tw = toks.take(3);

        let n = tw.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(tw.as_iter().collect::<String>(), "");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take(3);

        tw.parse::<u8, String>().unwrap_err();
        assert_eq!(tw.as_iter().collect::<String>(), "345");
    }
}
