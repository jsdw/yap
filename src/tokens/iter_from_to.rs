use crate::Tokens;

pub struct IterFromTo<'a, T: Tokens> {
    tokens: &'a mut T,
    original: T::Location,
    started: bool,
    from: T::Location,
    to: T::Location
}

impl <'a, T: Tokens> IterFromTo<'a, T> {
    pub(crate) fn new(tokens: &'a mut T, current: T::Location, from: T::Location, to: T::Location) -> IterFromTo<'a, T> {
        IterFromTo {
            tokens,
            original: current,
            from,
            to,
            started: false,
        }
    }
}

impl <'a, T: Tokens> Iterator for IterFromTo<'a, T> {
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        // Initial prep:
        if !self.started {
            self.tokens.set_location(self.from.clone());
            self.started = true;
        }

        // Once we hit the "to" location we return None
        // (this isn't an inclusive iterator).
        if self.tokens.is_at_location(&self.to) {
            None
        } else {
            self.tokens.next()
        }
    }
}

impl <'a, T: Tokens> Drop for IterFromTo<'a, T> {
    fn drop(&mut self) {
        // Reset the location on drop so that the tokens 
        // remain unaffected by this iterator:
        self.tokens.set_location(self.original.clone());
    }
}