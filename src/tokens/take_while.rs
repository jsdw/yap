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

    // Allow toks.take_while(..).parse(..) to be optimised.
    fn parse<Out, Buf>(&mut self) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        let res = self
            .tokens
            .parse_take_while::<Out, Buf, _>(&mut self.take_while);
        // Assume that underlying token location has been updated properly,
        // Avoid doing another check here, assuming that it's complete now anyway.
        if res.is_ok() {
            self.done = true;
        }
        res
    }
    // Allow toks.take_while(..).take_while(..).parse(..) to be optimised.
    fn parse_take_while<Out, Buf, F2>(
        &mut self,
        mut take_while: F2,
    ) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
        F2: FnMut(&Self::Item) -> bool,
    {
        self.tokens.parse_take_while::<Out, Buf, _>(|t| {
            // Only take while this and the child's take_while fn are both true.
            (self.take_while)(t) && take_while(t)
        })
    }
    // Allow toks.take_while(..).take(..).parse(..) to be optimised.
    fn parse_take<Out, Buf>(
        &mut self,
        mut n: usize,
    ) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        self.tokens.parse_take_while::<Out, Buf, _>(|t| {
            // Only take while this take_while fn is true for up to n tokens.
            let r = n != 0 && (self.take_while)(t);
            n = n.saturating_sub(1);
            r
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{types::IterTokens, IntoTokens, Tokens};

    #[test]
    fn test_parse_success() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take_while(|t| t.is_numeric());

        let n = tw.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(tw.collect::<String>(), "");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take_while(|t| t.is_numeric());

        tw.parse::<u8, String>().unwrap_err();
        assert_eq!(tw.collect::<String>(), "345");
    }

    #[test]
    fn test_combinator_stacking_optimisations() {
        const TOKS: &str = "345abc+";

        fn take_while(mut toks: impl Tokens<Item = char>) {
            let s: String = toks
                .take_while(|t| t.is_alphanumeric())
                .take_while(|t| t.is_numeric())
                .collect();

            assert_eq!(s, "345");
            assert_eq!(toks.collect::<String>(), "abc+");
        }
        fn take(mut toks: impl Tokens<Item = char>) {
            let s: String = toks.take_while(|t| t.is_alphanumeric()).take(4).collect();

            assert_eq!(s, "345a");
            assert_eq!(toks.collect::<String>(), "bc+");
        }

        take_while(TOKS.into_tokens());
        take_while(IterTokens::new(TOKS.chars()));

        take(TOKS.into_tokens());
        take(IterTokens::new(TOKS.chars()));
    }
}
