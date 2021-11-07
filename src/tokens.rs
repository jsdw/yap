/*! 
This module contains the core [`Tokens`] trait, which adds various convenience methods
to the standard [`Iterator`] interface aimed at making it easy to parse the input.

The [`IntoTokens`] trait is implemented for types that can be converted into something
implementing the [`Tokens`] trait (for example `&str` and `&[T]`). 
*/
use std::borrow::Borrow;

pub trait Tokens: Iterator {

    /// An object which can be used to reset the token stream 
    /// to some position.
    type Location: TokenLocation + PartialEq;

    /// Return a "location" that you can later pass to [`Tokens::rewind_to_location`]
    /// to reset the tokens back to the state at the time it was handed out.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcde".into_tokens();
    ///
    /// let location = s.location();
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.consumed().len(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.consumed().len(), 2);
    ///
    /// s.rewind_to_location(location);
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.consumed().len(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.consumed().len(), 2);
    /// ```
    fn location(&self) -> Self::Location;

    /// Reset the tokens to the location provided. If you provide a location that
    /// is in the future, expect that this could panic (implementation dependent).
    ///
    /// See [`Tokens::location`].
    fn rewind_to_location(&mut self, location: Self::Location);

    /// Return true if the current cursor location matches the location given, or false
    /// otherwise.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    /// 
    /// let mut s = "abc".into_tokens();
    /// let location = s.location();
    /// assert_eq!(s.is_at_location(location), true);
    /// s.next();
    /// assert_eq!(s.is_at_location(location), false);
    /// s.rewind_to_location(location);
    /// assert_eq!(s.is_at_location(location), true);
    /// ```
    fn is_at_location(&self, location: Self::Location) -> bool;

    /// Get back the next item in the input without consuming it.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.peek(), Some('a'));
    /// assert_eq!(s.peek(), Some('a'));
    /// ```
    fn peek(&mut self) -> Option<Self::Item> {
        let location = self.location();
        let item = self.next();
        self.rewind_to_location(location);
        item
    }

    /// Expect a specific token to be next. If the token is not found, the iterator is not 
    /// advanced.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.token(&'a'), true);
    /// assert_eq!(s.token(&'b'), true);
    /// assert_eq!(s.token('z'), false);
    /// assert_eq!(s.token('y'), false);
    /// assert_eq!(s.token('c'), true);
    /// ```
    fn token<I>(&mut self, t: I) -> bool
    where 
        Self::Item: PartialEq,
        I: Borrow<Self::Item>
    {
        let location = self.location();
        match self.next() {
            Some(item) if &item == t.borrow() => true,
            _ => {
                self.rewind_to_location(location);
                false
            }
        }
    }

    /// Expect a specific set of tokens to be next. If the tokens are not found, the iterator is not 
    /// advanced. Anything that implements `IntoIterator` with an `Item` type that can be borrowed to
    /// produce `&Item` can be provided as an input to this.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcdef".into_tokens();
    /// 
    /// assert_eq!(s.tokens("abc".chars()), true);
    /// assert_eq!(s.remaining(), "def");
    /// 
    /// assert_eq!(s.tokens("de".chars()), true);
    /// assert_eq!(s.remaining(), "f");
    /// ```
    fn tokens<It>(&mut self, ts: It) -> bool
    where 
        Self::Item: PartialEq,
        It: IntoIterator,
        It::Item: Borrow<Self::Item>
    {
        let location = self.location();
        // `ts` comes first to avoid consuming an extra item from self before 
        // realising that it's time to stop..
        for (expected, actual) in ts.into_iter().zip(self.into_iter()) {
            if &actual != expected.borrow() {
                self.rewind_to_location(location);
                return false;
            }
        }
        true
    }

    /// Return the first token that matches the tokens provided, or None if none of them
    /// match.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcdef".into_tokens();
    ///
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('a'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('b'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), Some('c'));
    /// assert_eq!(s.one_of_tokens("abc".chars()), None);
    /// assert_eq!(s.remaining(), "def");
    /// ```
    fn one_of_tokens<It>(&mut self, ts: It) -> Option<Self::Item>
    where 
        Self::Item: PartialEq,
        It: IntoIterator,
        It::Item: Borrow<Self::Item>
    {
        for expected in ts.into_iter() {
            let location = self.location();
            match self.next() {
                Some(token) if &token == expected.borrow() => {
                    return Some(token)
                },
                _ => {
                    self.rewind_to_location(location);
                }
            }
        }
        None
    }

    /// Parse 0 or more instances of some parser, returning all of the successfully parsed
    /// output and leaving any input that was not successfully parsed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "12345abcde".into_tokens();
    /// let digits = s.many(|t| parse_digit(t));
    ///
    /// assert_eq!(digits, vec![1,2,3,4,5]);
    /// assert_eq!(s.remaining(), "abcde");
    /// ```
    fn many<F, Output>(&mut self, mut parser: F) -> Vec<Output> 
    where F: FnMut(&mut Self) -> Option<Output>
    {
        let mut out = vec![];
        loop {
            let pos = self.location();
            if let Some(output) = parser(self) {
                out.push(output);
            } else {
                // The provided parser failed to produce more output,
                // so rewind to before it and end.
                self.rewind_to_location(pos);
                break out;
            }
        }
    }

    /// Parse 1 or more instances of some parser, returning all of the successfully parsed
    /// output and leaving any input that was not successfully parsed. If the provided parser
    /// fails immediately, return the error that it produced.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// // Parse all of the digits that we can. Note that `many1` expects
    /// // a Result to be returned from out parser now, in case we want to
    /// // return the error we encountered.
    /// let mut s = "12345abcde".into_tokens();
    /// let digits = s.many1(|t| parse_digit(t).ok_or("aaah"));
    /// assert_eq!(digits, Ok(vec![1,2,3,4,5]));
    /// assert_eq!(s.remaining(), "abcde");
    ///
    /// // No digits at all; this won't work! `many` would just return an
    /// // empty Vec, but `many1` gives us back the error we encountered.
    /// let mut s = "abcde".into_tokens();
    /// let digits = s.many1(|t| parse_digit(t).ok_or("aaah"));
    /// assert_eq!(digits, Err("aaah"));
    /// assert_eq!(s.remaining(), "abcde");
    /// ```
    fn many1<F, E, Output>(&mut self, mut parser: F) -> Result<Vec<Output>, E> 
    where F: FnMut(&mut Self) -> Result<Output, E>
    {
        let mut out = vec![];
        loop {
            let pos = self.location();
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                },
                Err(e) => {
                    self.rewind_to_location(pos);
                    if out.is_empty() {
                        break Err(e)
                    } else {                    
                        break Ok(out);
                    }
                },
            }
        }
    }

    /// Ignore 0 or more instances of some parser.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// struct ABC;
    /// fn parse_abc(mut tokens: impl Tokens<Item=char>) -> Option<ABC> {
    ///     let a = tokens.next()?;
    ///     let b = tokens.next()?;
    ///     let c = tokens.next()?;
    ///     if a == 'a' && b == 'b' && c == 'c' {
    ///         Some(ABC)
    ///     } else {
    ///         None
    ///     }
    /// }
    ///
    /// let mut s = "abcabcababab".into_tokens();
    /// s.skip_many(|t| parse_abc(t).is_some());
    ///
    /// assert_eq!(s.remaining(), "ababab");
    /// ```
    fn skip_many<F>(&mut self, mut parser: F)
    where F: FnMut(&mut Self) -> bool
    {
        loop {
            let pos = self.location();
            if !parser(self) {
                // The provided parser failed to produce more output,
                // so rewind to before it and end.
                self.rewind_to_location(pos);
                break;
            }
        }
    }

    /// Ignore 1 or more instances of some parser. If the provided parser
    /// fails immediately, return the error that it produced.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// struct ABC;
    /// fn parse_abc(mut tokens: impl Tokens<Item=char>) -> Option<ABC> {
    ///     let a = tokens.next()?;
    ///     let b = tokens.next()?;
    ///     let c = tokens.next()?;
    ///     if a == 'a' && b == 'b' && c == 'c' {
    ///         Some(ABC)
    ///     } else {
    ///         None
    ///     }
    /// }
    ///
    /// let mut s = "ababababcabc".into_tokens();
    /// let digits = s.skip_many1(|t| parse_abc(t).ok_or("aaah"));
    ///
    /// assert_eq!(digits, Err("aaah"));
    /// assert_eq!(s.remaining(), "ababababcabc");
    /// ```
    fn skip_many1<F, E, Ignored>(&mut self, mut parser: F) -> Result<(), E> 
    where F: FnMut(&mut Self) -> Result<Ignored, E>
    {
        let mut has_seen = false;
        loop {
            let pos = self.location();
            if let Err(e) = parser(self) {
                self.rewind_to_location(pos);
                if !has_seen {
                    break Err(e)
                } else {                    
                    break Ok(());
                }
            } else {
                has_seen = true;
            }
        }
    }

    /// Iterate over the tokens until the provided function returns false on a token.
    /// Only consume the tokens that the function returned true for, and return them.
    /// 
    /// [`Iterator::take_while`] consumes the input, and so this method is more useful
    /// if you'd like to continue iterating/parsing more input after running it. 
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// let digits = s.take_tokens_while(|c| c.is_numeric());
    /// assert_eq!(digits, vec!['1','2','3','4','5']);
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    fn take_tokens_while<F>(&mut self, mut f: F) -> Vec<Self::Item> 
    where F: FnMut(&Self::Item) -> bool
    {
        let mut toks = vec![];
        loop {
            let pos = self.location();
            match self.next() {
                Some(item) if f(&item) => toks.push(item),
                _ => {
                    self.rewind_to_location(pos);
                    break toks;
                }
            }
        }
    }

    /// Iterate over the tokens until the provided function returns true on one.
    /// Only consume the tokens that the function returned false for, and return them.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc12345".into_tokens();
    /// let digits = s.take_tokens_until(|c| c.is_numeric());
    /// assert_eq!(digits, vec!['a', 'b', 'c']);
    /// assert_eq!(s.remaining(), "12345");
    /// ```
    fn take_tokens_until<F>(&mut self, mut f: F) -> Vec<Self::Item> 
    where F: FnMut(&Self::Item) -> bool
    {
        self.take_tokens_while(|t| !f(t))
    }

    /// Iterate over the tokens until the provided function returns false on one.
    /// Only consume the tokens that the function returned true for, ignoring them.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "12345abc".into_tokens();
    /// s.skip_tokens_while(|c| c.is_numeric());
    /// assert_eq!(s.remaining(), "abc");
    /// ```
    fn skip_tokens_while<F>(&mut self, mut f: F)
    where F: FnMut(&Self::Item) -> bool
    {
        loop {
            let pos = self.location();
            match self.next() {
                Some(item) if f(&item) => { /* item found; keep going */ }
                _ => {
                    self.rewind_to_location(pos);
                    break;
                }
            }
        }
    }

    /// Iterate over the tokens until the provided function returns true on one.
    /// Only consume the tokens that the function returned false for, ignoring them.
    /// 
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abc12345".into_tokens();
    /// s.skip_tokens_until(|c| c.is_numeric());
    /// assert_eq!(s.remaining(), "12345");
    /// ```
    fn skip_tokens_until<F>(&mut self, mut f: F)
    where F: FnMut(&Self::Item) -> bool
    {
        self.skip_tokens_while(|t| !f(t))
    }

    /// Parses anything matching the `parser` function, and expects to parse something
    /// matching the `separator` function between each one.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1,2,3,4,abc".into_tokens();
    /// let digits = s.sep_by(|t| parse_digit(t), |t| t.token(','));
    /// assert_eq!(digits, vec![1,2,3,4]);
    /// assert_eq!(s.remaining(), ",abc");
    /// ```
    fn sep_by<F, S, Output>(&mut self, mut parser: F, mut separator: S) -> Vec<Output> 
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> bool
    {
        let mut out = vec![];
        let mut last_out_pos = self.location();
        loop {
            match parser(self) {
                Some(output) => {
                    out.push(output);
                    last_out_pos = self.location();
        
                    if !separator(self) {
                        // No separator? rewind to after the last output and return
                        // what we have so far.
                        self.rewind_to_location(last_out_pos);
                        break out;
                    }
                }
                None => {
                    // No output? We may have parsed a separator last time round!
                    // Revert to after last output and return what we have.
                    self.rewind_to_location(last_out_pos);
                    break out;
                }
            }
        }
    }

    /// Parses anything matching the `parser` function, and expects to parse something
    /// matching the `separator` function between each one. Returns the first parse error
    /// encountered if no items are successfully parsed.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "a,1,2,3".into_tokens();
    /// let digits = s.sep_by1(|t| parse_digit(t).ok_or("aah"), |t| t.token(','));
    /// assert_eq!(digits, Err("aah"));
    /// assert_eq!(s.remaining(), "a,1,2,3");
    /// ```
    fn sep_by1<F, S, E, Output>(&mut self, mut parser: F, mut separator: S) -> Result<Vec<Output>, E> 
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> bool
    {
        let mut out = vec![];
        let mut last_out_pos = self.location();
        loop {
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                    last_out_pos = self.location();
            
                    if !separator(self) {
                        // No separator? rewind to after the last output and return
                        // what we have so far.
                        self.rewind_to_location(last_out_pos);
                        break Ok(out);
                    }
                },
                Err(e) => {
                    // Reset to last output parsed. Return error if no output 
                    // was successfully parsed at all.
                    self.rewind_to_location(last_out_pos);
                    break if out.is_empty() { Err(e) } else { Ok(out) };
                }
            }
        }
    }

    /// Parses anything matching the `parser` function, and expects to parse something
    /// matching the `separator` function between each one.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// #[derive(PartialEq,Debug)]
    /// enum Op { Plus, Minus, Divide }
    /// #[derive(PartialEq,Debug)]
    /// enum OpOrDigit { Op(Op), Digit(u32) }
    ///
    /// fn parse_op(mut t: impl Tokens<Item=char>) -> Option<Op> {
    ///     match t.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    ///
    /// fn parse_digit(mut tokens: impl Tokens<Item=char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1+2/3-4+abc".into_tokens();
    /// let output = s.sep_by_all(
    ///     |t| parse_digit(t).map(OpOrDigit::Digit), 
    ///     |t| parse_op(t).map(OpOrDigit::Op)
    /// );
    /// assert_eq!(output, vec![
    ///     OpOrDigit::Digit(1),
    ///     OpOrDigit::Op(Op::Plus),
    ///     OpOrDigit::Digit(2),
    ///     OpOrDigit::Op(Op::Divide),
    ///     OpOrDigit::Digit(3),
    ///     OpOrDigit::Op(Op::Minus),
    ///     OpOrDigit::Digit(4),
    /// ]);
    /// assert_eq!(s.remaining(), "+abc");
    /// ```
    fn sep_by_all<F, S, Output>(&mut self, mut parser: F, mut separator: S) -> Vec<Output> 
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> Option<Output>
    {
        let mut out = vec![];
        let mut last_out_pos = self.location();
        loop {
            match parser(self) {
                Some(output) => {
                    out.push(output);
                    last_out_pos = self.location();
        
                    match separator(self) {
                        Some(sep) => {
                            // Push our separator output to the list, too.
                            out.push(sep);
                        },
                        None => {
                            // No separator? rewind to after the last output and return
                            // what we have so far.
                            self.rewind_to_location(last_out_pos);
                            break out;
                        }
                    }
                }
                None => {
                    // No output? We're either just starting, or we just parsed a separator,
                    // so rewind and throw away the mis-parsed separator (if there is one).
                    out.pop();
                    self.rewind_to_location(last_out_pos);
                    break out;
                }
            }
        }
    }
    
    /// Identical to [`Tokens::sep_by_all`], except that if we fail to parse the first item, we
    /// return the error that we ran into trying to do so, instead of returning an empty Vec.
    fn sep_by1_all<F, S, E, Output>(&mut self, mut parser: F, mut separator: S) -> Result<Vec<Output>, E> 
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> Option<Output>
    {
        let mut out = vec![];
        let mut last_out_pos = self.location();
        loop {
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                    last_out_pos = self.location();
            
                    match separator(self) {
                        Some(sep) => {
                            // Push our separator output to the list, too.
                            out.push(sep);
                        },
                        None => {
                            // No separator? rewind to after the last output and return
                            // what we have so far.
                            self.rewind_to_location(last_out_pos);
                            break Ok(out);
                        }
                    }
                },
                Err(e) => {
                    // Reset to last output parsed. Return error if no output 
                    // was successfully parsed at all.
                    self.rewind_to_location(last_out_pos);
                    break if out.is_empty() { Err(e) } else { Ok(out) };
                }
            }
        }
    }

    /// Parse some tokens optionally surrounded by the tokens consumed by the surrounding parser.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "   hello    ".into_tokens();
    ///
    /// let hello: String = s.surrounded_by(
    ///     |t| t.take_tokens_while(|c| c.is_ascii_alphabetic()).into_iter().collect(),
    ///     |t| t.skip_tokens_while(|c| c.is_ascii_whitespace())
    /// );
    ///
    /// assert_eq!(&*hello, "hello");
    /// assert_eq!(s.remaining(), "");
    /// ```
    fn surrounded_by<F, S, Output>(&mut self, mut parser: F, mut surrounding: S) -> Output 
    where
        F: FnMut(&mut Self) -> Output,
        S: FnMut(&mut Self)
    {
        self.skip_optional(&mut surrounding);
        let res = parser(self);
        self.skip_optional(&mut surrounding);
        res
    }

    /// Attempt to parse some output from the tokens. If the function returns `None`,
    /// don't consume any input. Else, return whatever the function produced.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "foobar".into_tokens();
    ///
    /// let res = s.optional(|s| {
    ///     let a = s.next();
    ///     let b = s.next();
    ///     if a == b {
    ///         Some("yay")
    ///     } else {
    ///         None
    ///     }
    /// });
    ///
    /// // nothing consumed since None returned from fn
    /// assert_eq!(s.remaining(), "foobar");
    /// assert_eq!(res, None);
    ///
    /// let res = s.optional(|s| {
    ///     let a = s.next()?;
    ///     let b = s.next()?;
    ///     Some((a, b))
    /// });
    ///
    /// // 2 chars consumed since Some returned from fn
    /// assert_eq!(s.remaining(), "obar");
    /// assert_eq!(res, Some(('f', 'o')));
    /// ```
    fn optional<F, Output>(&mut self, mut f: F) -> Option<Output> 
    where F: FnMut(&mut Self) -> Option<Output> {
        let location = self.location();
        match f(self) {
            Some(output) => Some(output),
            None => {
                self.rewind_to_location(location);
                None
            }
        }
    }

    /// Run a parser against some tokens, and don't care whether it succeeded
    /// or how much input it consumed.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "   helloworld".into_tokens();
    ///
    /// fn parse_whitespace(mut t: impl Tokens<Item=char>) {
    ///     t.skip_tokens_while(|c| c.is_ascii_whitespace());
    /// }
    ///
    /// s.skip_optional(|t| parse_whitespace(t));
    /// let is_hello = s.tokens("hello".chars());
    /// s.skip_optional(|t| parse_whitespace(t));
    /// let world: String = s.take_tokens_while(|c| c.is_ascii_alphabetic()).into_iter().collect();
    ///
    /// // assert_eq!(is_hello, true);
    /// // assert_eq!(&*world, "world");
    /// ```
    fn skip_optional<F>(&mut self, mut f: F)
    where F: FnMut(&mut Self) {
        self.optional(|t| {
            f(t);
            Some(())
        });
    }

}

pub trait TokenLocation {
    /// Return the current offset into the tokens that we've parsed up to so far.
    /// The exact meaning of this can vary by implementation; when parsing slices, it
    /// is index of the slice item we've consumed up to (it may equal `slice.len()`), and when
    /// parsing `&str`'s it is the number of bytes (not characters) consumed so far.
    /// 
    /// # Example
    /// 
    /// ```
    /// use yap::{ Tokens, IntoTokens, TokenLocation };
    /// 
    /// let mut s = "abc".into_tokens();
    /// assert_eq!(s.location().offset(), 0);
    /// s.next();
    /// assert_eq!(s.location().offset(), 1);
    /// s.next();
    /// assert_eq!(s.location().offset(), 2);
    /// ```
    fn offset(&self) -> usize;
}

impl <'a, T> Tokens for &'a mut T 
where T: Tokens
{
    type Location = T::Location;

    fn location(&self) -> Self::Location {
        <T as Tokens>::location(self)
    }
    fn rewind_to_location(&mut self, location: Self::Location) {
        <T as Tokens>::rewind_to_location(self, location)
    }
    fn is_at_location(&self, location: Self::Location) -> bool {
        <T as Tokens>::is_at_location(self, location)
    }
}

/// A trait that is implemented by anything which can be converted into an 
/// object implementing the [`Tokens`] trait.
pub trait IntoTokens<Item> {
    type Tokens: Tokens<Item=Item>;
    fn into_tokens(self) -> Self::Tokens;
}


#[cfg(test)]
mod test {

    use super::*;
    use crate::parse;

    #[derive(Debug, PartialEq)]
    struct AB;

    // A simple parser that looks for "ab" in an input token stream.
    // Notably, it doesn't try to rewind on failure. We expect the *many*
    // combinators to take care of that sort of thing for us as needed.
    fn parse_ab(mut t: impl Tokens<Item=char>) -> Option<AB> {
        // match any sequence "ab".
        let a = t.next()?;
        let b = t.next()?;
        if a == 'a' && b == 'b' {
            Some(AB)
        } else {
            None
        }
    }

    #[test]
    fn test_many() {
        let (abs, rest) = parse("acabab", |mut t| {
            // Get as many ABs as we can from the input:
            let abs = t.many(|t| parse_ab(t));
            // Return the parsed "ab"s and whatever is remaining.
            Ok::<_,()>((abs, t.collect::<Vec<char>>()))
        }).unwrap();

        assert_eq!(abs.len(), 0);
        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        let (abs, rest) = parse("abababaa", |mut t| {
            let abs = t.many(|t| parse_ab(t));
            Ok::<_,()>((abs, t.collect::<Vec<char>>()))
        }).unwrap();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a', 'a']);

        let (abs, rest) = parse("abababa", |mut t| {
            let abs = t.many(|t| parse_ab(t));
            Ok::<_,()>((abs, t.collect::<Vec<char>>()))
        }).unwrap();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    fn test_many1() {
        // Need at least 1 successful parse, or error from parser is returned.
        let res = parse("acabab", |mut t| {
            t.many1(|t| parse_ab(t).ok_or("Could not parse ab!"))
        });
        assert_eq!(res, Err("Could not parse ab!"));

        let (abs, rest) = parse("abababaa", |mut t| {
            let abs = t.many1(|t| parse_ab(t).ok_or(()))?;
            Ok::<_,()>((abs, t.collect::<Vec<char>>()))
        }).unwrap();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a', 'a']);

        let (abs, rest) = parse("abababa", |mut t| {
            let abs = t.many1(|t| parse_ab(t).ok_or(()))?;
            Ok::<_,()>((abs, t.collect::<Vec<char>>()))
        }).unwrap();

        assert_eq!(abs.len(), 3);
        assert_eq!(rest, vec!['a']);
    }

    #[test]
    fn test_skip_many() {
        let rest = parse("acabab", |mut t| {
            // Skip as many ABs as we can from the input:
            t.skip_many(|t| parse_ab(t).is_some());
            // Return whatever is remaining.
            Ok::<_,()>(t.collect::<Vec<char>>())
        }).unwrap();

        assert_eq!(rest, vec!['a', 'c', 'a', 'b', 'a', 'b']);

        let rest = parse("ababaab", |mut t| {
            t.skip_many(|t| parse_ab(t).is_some());
            Ok::<_,()>(t.collect::<Vec<char>>())
        }).unwrap();

        assert_eq!(rest, vec!['a', 'a', 'b']);
    }

    #[test]
    fn test_skip_many1() {
        let rest = parse("acabab", |mut t| {
            // Skip as many ABs as we can from the input:
            t.skip_many1(|t| parse_ab(t).ok_or("Can't parse AB"))?;
            // Return whatever is remaining.
            Ok::<_,&str>(t.collect::<Vec<char>>())
        });

        assert_eq!(rest, Err("Can't parse AB"));

        let rest = parse("ababaab", |mut t| {
            t.skip_many1(|t| parse_ab(t).ok_or(()))?;
            Ok::<_,()>(t.collect::<Vec<char>>())
        }).unwrap();

        assert_eq!(rest, vec!['a', 'a', 'b']);
    }

}