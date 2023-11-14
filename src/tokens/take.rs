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

impl<'a, T> Tokens for Take<'a, T>
where
    T: Tokens,
{
    type Item = T::Item;
    type Location = T::Location;

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

    fn location(&self) -> Self::Location {
        self.tokens.location()
    }

    fn set_location(&mut self, location: Self::Location) {
        self.tokens.set_location(location)
    }

    fn is_at_location(&self, location: &Self::Location) -> bool {
        self.tokens.is_at_location(location)
    }

    // Allow toks.take(..).parse(..) to be optimised.
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
    // Allow toks.take(..).take_while(..).parse(..) to be optimised.
    fn parse_take_while<Out, Buf, F2>(
        &mut self,
        mut take_while: F2,
    ) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
        F2: FnMut(&Self::Item) -> bool,
    {
        let mut n = self.n;
        let res = self.tokens.parse_take_while::<Out, Buf, _>(|t| {
            // Go until we run out of items from this take() or if the take_while
            // fn returns false.
            let res = n > 0 && take_while(t);
            n = n.saturating_sub(1);
            res
        });

        // If this works, then we don't have so many tokens left to iter here:
        if res.is_ok() {
            self.n = n;
        }
        res
    }
    // Allow toks.take(..).take(..).parse(..) to be optimised.
    fn parse_take<Out, Buf>(&mut self, n: usize) -> Result<Out, <Out as core::str::FromStr>::Err>
    where
        Out: core::str::FromStr,
        Buf: FromIterator<Self::Item> + core::ops::Deref<Target = str>,
    {
        // If we call take().take(), just use the minimum of the two n's.
        let min_n = usize::min(self.n, n);
        let res = self.tokens.parse_take::<Out, Buf>(min_n);

        // If this works, then we don't have so many tokens left to iter here:
        if res.is_ok() {
            self.n -= min_n;
        }
        res
    }
}

#[cfg(test)]
mod test {
    use crate::{types::IterTokens, IntoTokens, Tokens};

    #[test]
    fn test_parse_success() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take(3);

        let n = tw.parse::<u16, String>().unwrap();
        assert_eq!(n, 345);
        assert_eq!(tw.collect::<String>(), "");
    }

    #[test]
    fn test_parse_failure() {
        let mut toks = "345abc".into_tokens();

        let mut tw = toks.take(3);

        tw.parse::<u8, String>().unwrap_err();
        assert_eq!(tw.collect::<String>(), "345");
    }

    #[test]
    fn test_combinator_stacking_optimisations() {
        const TOKS: &str = "345abc+";

        fn take_while(mut toks: impl Tokens<Item = char>) {
            let s: String = toks.take(6).take_while(|t| t.is_numeric()).collect();

            assert_eq!(s, "345");
            assert_eq!(toks.collect::<String>(), "abc+");
        }
        fn take(mut toks: impl Tokens<Item = char>) {
            let s: String = toks.take(6).take(4).collect();

            assert_eq!(s, "345a");
            assert_eq!(toks.collect::<String>(), "bc+");
        }

        take_while(TOKS.into_tokens());
        take_while(IterTokens::new(TOKS.chars()));

        take(TOKS.into_tokens());
        take(IterTokens::new(TOKS.chars()));
    }
}
