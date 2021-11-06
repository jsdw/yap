/*! 
This module contains the core [`Tokens`] trait, which adds various convenience methods
to the standard [`Iterator`] interface aimed at making it easy to parse the input.

The [`IntoTokens`] trait is implemented for types that can be converted into something
implementing the [`Tokens`] trait (for example `&str` and `&[T]`). 
*/
use std::borrow::Borrow;

pub trait Tokens<Item>: Iterator<Item=Item> {
    /// An object which can be used to reset the token stream 
    /// to some position.
    type CheckPoint;

    /// The current index into the token stream.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcde".into_tokens();
    /// s.next().unwrap();
    /// assert_eq!(s.offset(), 1);
    /// s.next().unwrap();
    /// assert_eq!(s.offset(), 2);
    /// ```
    fn offset(&self) -> usize;

    /// Return a "checkpoint" that you can later pass to [`Tokens::rewind_to_checkpoint`]
    /// to reset the tokens back to the state at the time it was handed out.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// let mut s = "abcde".into_tokens();
    ///
    /// let checkpoint = s.save_checkpoint();
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.offset(), 2);
    ///
    /// s.rewind_to_checkpoint(checkpoint);
    ///
    /// assert_eq!(s.next().unwrap(), 'a');
    /// assert_eq!(s.offset(), 1);
    /// assert_eq!(s.next().unwrap(), 'b');
    /// assert_eq!(s.offset(), 2);
    /// ```
    fn save_checkpoint(&self) -> Self::CheckPoint;

    /// Reset the tokens to the checkpoint provided. If you provide a checkpoint that
    /// is in the future, expect that this could panic (implementation dependent).
    ///
    /// See [`Tokens::save_checkpoint`].
    fn rewind_to_checkpoint(&mut self, checkpoint: Self::CheckPoint);

    /**
    Expect a specific token to be next. If the token is not found, the iterator is not 
    advanced.

    # Example

    ```
    use yap::{ Tokens, IntoTokens };

    let mut s = "abc".into_tokens();
    assert_eq!(s.token(&'a'), Some('a'));
    assert_eq!(s.token(&'b'), Some('b'));
    assert_eq!(s.token('z'), None);
    assert_eq!(s.token('y'), None);
    assert_eq!(s.token('c'), Some('c'));
    ```
    */
    fn token<I>(&mut self, t: I) -> Option<Item> 
    where 
        Item: PartialEq,
        I: Borrow<Item>
    {
        let checkpoint = self.save_checkpoint();
        match self.next() {
            Some(item) if &item == t.borrow() => {
                Some(item)
            },
            _ => {
                self.rewind_to_checkpoint(checkpoint);
                None
            }
        }
    }

    /// Parse 0 or more instances of some parser, returning all of the successfully parsed
    /// output and leaving any input that was not successfully parsed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use yap::{ Tokens, IntoTokens };
    ///
    /// fn parse_digit(mut tokens: impl Tokens<char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "12345abcde".into_tokens();
    /// let digits = s.many(|t| parse_digit(t));
    ///
    /// assert_eq!(digits, vec![1,2,3,4,5]);
    /// assert_eq!(s.str_remaining(), "abcde");
    /// ```
    fn many<F, Output>(&mut self, mut parser: F) -> Vec<Output> 
    where F: FnMut(&mut Self) -> Option<Output>
    {
        let mut out = vec![];
        loop {
            let pos = self.save_checkpoint();
            if let Some(output) = parser(self) {
                out.push(output);
            } else {
                // The provided parser failed to produce more output,
                // so rewind to before it and end.
                self.rewind_to_checkpoint(pos);
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
    /// fn parse_digit(mut tokens: impl Tokens<char>) -> Option<u32> {
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
    /// assert_eq!(s.str_remaining(), "abcde");
    ///
    /// // No digits at all; this won't work! `many` would just return an
    /// // empty Vec, but `many1` gives us back the error we encountered.
    /// let mut s = "abcde".into_tokens();
    /// let digits = s.many1(|t| parse_digit(t).ok_or("aaah"));
    /// assert_eq!(digits, Err("aaah"));
    /// assert_eq!(s.str_remaining(), "abcde");
    /// ```
    fn many1<F, E, Output>(&mut self, mut parser: F) -> Result<Vec<Output>, E> 
    where F: FnMut(&mut Self) -> Result<Output, E>
    {
        let mut out = vec![];
        loop {
            let pos = self.save_checkpoint();
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                },
                Err(e) => {
                    self.rewind_to_checkpoint(pos);
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
    /// fn parse_abc(mut tokens: impl Tokens<char>) -> Option<ABC> {
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
    /// assert_eq!(s.str_remaining(), "ababab");
    /// ```
    fn skip_many<F>(&mut self, mut parser: F)
    where F: FnMut(&mut Self) -> bool
    {
        loop {
            let pos = self.save_checkpoint();
            if !parser(self) {
                // The provided parser failed to produce more output,
                // so rewind to before it and end.
                self.rewind_to_checkpoint(pos);
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
    /// fn parse_abc(mut tokens: impl Tokens<char>) -> Option<ABC> {
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
    /// assert_eq!(s.str_remaining(), "ababababcabc");
    /// ```
    fn skip_many1<F, E, Ignored>(&mut self, mut parser: F) -> Result<(), E> 
    where F: FnMut(&mut Self) -> Result<Ignored, E>
    {
        let mut has_seen = false;
        loop {
            let pos = self.save_checkpoint();
            if let Err(e) = parser(self) {
                self.rewind_to_checkpoint(pos);
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
    /// assert_eq!(s.str_remaining(), "abc");
    /// ```
    fn take_tokens_while<F>(&mut self, mut f: F) -> Vec<Item> 
    where F: FnMut(&Item) -> bool
    {
        let mut toks = vec![];
        loop {
            let pos = self.save_checkpoint();
            if let Some(item) = self.next() {
                if f(&item) {
                    toks.push(item);
                } else {
                    self.rewind_to_checkpoint(pos);
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
    /// assert_eq!(s.str_remaining(), "12345");
    /// ```
    fn take_tokens_until<F>(&mut self, mut f: F) -> Vec<Item> 
    where F: FnMut(&Item) -> bool
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
    /// assert_eq!(s.str_remaining(), "abc");
    /// ```
    fn skip_tokens_while<F>(&mut self, mut f: F)
    where F: FnMut(&Item) -> bool
    {
        loop {
            let pos = self.save_checkpoint();
            if let Some(item) = self.next() {
                if f(&item) {
                    // item found; keep going
                } else {
                    self.rewind_to_checkpoint(pos);
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
    /// assert_eq!(s.str_remaining(), "12345");
    /// ```
    fn skip_tokens_until<F>(&mut self, mut f: F)
    where F: FnMut(&Item) -> bool
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
    /// fn parse_digit(mut tokens: impl Tokens<char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "1,2,3,4,abc".into_tokens();
    /// let digits = s.sep_by(|t| parse_digit(t), |t| t.token(',').is_some());
    /// assert_eq!(digits, vec![1,2,3,4]);
    /// assert_eq!(s.str_remaining(), ",abc");
    /// ```
    fn sep_by<F, S, Output>(&mut self, mut parser: F, mut separator: S) -> Vec<Output> 
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> bool
    {
        let mut out = vec![];
        let mut last_out_pos = self.save_checkpoint();
        loop {
            match parser(self) {
                Some(output) => {
                    out.push(output);
                    last_out_pos = self.save_checkpoint();
        
                    if !separator(self) {
                        // No separator? rewind to after the last output and return
                        // what we have so far.
                        self.rewind_to_checkpoint(last_out_pos);
                        break out;
                    }
                }
                None => {
                    // No output? We may have parsed a separator last time round!
                    // Revert to after last output and return what we have.
                    self.rewind_to_checkpoint(last_out_pos);
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
    /// fn parse_digit(mut tokens: impl Tokens<char>) -> Option<u32> {
    ///     let c = tokens.next()?;
    ///     c.to_digit(10)
    /// }
    ///
    /// let mut s = "a,1,2,3".into_tokens();
    /// let digits = s.sep_by1(|t| parse_digit(t).ok_or("aah"), |t| t.token(',').is_some());
    /// assert_eq!(digits, Err("aah"));
    /// assert_eq!(s.str_remaining(), "a,1,2,3");
    /// ```
    fn sep_by1<F, S, E, Output>(&mut self, mut parser: F, mut separator: S) -> Result<Vec<Output>, E> 
    where
        F: FnMut(&mut Self) -> Result<Output, E>,
        S: FnMut(&mut Self) -> bool
    {
        let mut out = vec![];
        let mut last_out_pos = self.save_checkpoint();
        loop {
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                    last_out_pos = self.save_checkpoint();
            
                    if !separator(self) {
                        // No separator? rewind to after the last output and return
                        // what we have so far.
                        self.rewind_to_checkpoint(last_out_pos);
                        break Ok(out);
                    }
                },
                Err(e) => {
                    // Reset to last output parsed. Return error if no output 
                    // was successfully parsed at all.
                    self.rewind_to_checkpoint(last_out_pos);
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
    /// fn parse_op(mut t: impl Tokens<char>) -> Option<Op> {
    ///     match t.next()? {
    ///         '-' => Some(Op::Minus),
    ///         '+' => Some(Op::Plus),
    ///         '/' => Some(Op::Divide),
    ///         _ => None
    ///     }
    /// }
    ///
    /// fn parse_digit(mut tokens: impl Tokens<char>) -> Option<u32> {
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
    /// assert_eq!(s.str_remaining(), "+abc");
    /// ```
    fn sep_by_all<F, S, Output>(&mut self, mut parser: F, mut separator: S) -> Vec<Output> 
    where
        F: FnMut(&mut Self) -> Option<Output>,
        S: FnMut(&mut Self) -> Option<Output>
    {
        let mut out = vec![];
        let mut last_out_pos = self.save_checkpoint();
        loop {
            match parser(self) {
                Some(output) => {
                    out.push(output);
                    last_out_pos = self.save_checkpoint();
        
                    match separator(self) {
                        Some(sep) => {
                            // Push our separator output to the list, too.
                            out.push(sep);
                        },
                        None => {
                            // No separator? rewind to after the last output and return
                            // what we have so far.
                            self.rewind_to_checkpoint(last_out_pos);
                            break out;
                        }
                    }
                }
                None => {
                    // No output? We're either just starting, or we just parsed a separator,
                    // so rewind and throw away the mis-parsed separator (if there is one).
                    out.pop();
                    self.rewind_to_checkpoint(last_out_pos);
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
        let mut last_out_pos = self.save_checkpoint();
        loop {
            match parser(self) {
                Ok(output) => {
                    out.push(output);
                    last_out_pos = self.save_checkpoint();
            
                    match separator(self) {
                        Some(sep) => {
                            // Push our separator output to the list, too.
                            out.push(sep);
                        },
                        None => {
                            // No separator? rewind to after the last output and return
                            // what we have so far.
                            self.rewind_to_checkpoint(last_out_pos);
                            break Ok(out);
                        }
                    }
                },
                Err(e) => {
                    // Reset to last output parsed. Return error if no output 
                    // was successfully parsed at all.
                    self.rewind_to_checkpoint(last_out_pos);
                    break if out.is_empty() { Err(e) } else { Ok(out) };
                }
            }
        }
    }

}

impl <'a, Item, T> Tokens<Item> for &'a mut T 
where T: Tokens<Item>
{
    type CheckPoint = T::CheckPoint;

    fn offset(&self) -> usize {
        <T as Tokens<Item>>::offset(self)
    }
    fn save_checkpoint(&self) -> Self::CheckPoint {
        <T as Tokens<Item>>::save_checkpoint(self)
    }
    fn rewind_to_checkpoint(&mut self, checkpoint: Self::CheckPoint) {
        <T as Tokens<Item>>::rewind_to_checkpoint(self, checkpoint)
    }
}

/// A trait that is implemented by anything which can be converted into an 
/// object implementing the [`Tokens`] trait.
pub trait IntoTokens<Item> {
    type Tokens: Tokens<Item>;
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
    fn parse_ab(mut t: impl Tokens<char>) -> Option<AB> {
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