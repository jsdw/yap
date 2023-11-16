//! Helper functions for working with `Tokens<Item=char>`.

use crate::Tokens;

/// Some extra helper methods specific to parsing token iterators of chars.
pub trait CharTokens: Tokens<Item = char> {
    /// If the next tokens are either `\n` (like on linux)  or `\r\n` (like on windows),
    /// this will consume then and return `Some("\n")` or `Some("\r\n")` respectively.
    /// If the next tokens are not one of these, then `None` will be returned and nothing
    /// will be consumed.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, CharTokens};
    ///
    /// let mut toks = "\r\n abc".into_tokens();
    ///
    /// assert_eq!(toks.line_ending(), Some("\r\n"));
    /// assert_eq!(toks.remaining(), " abc");
    ///
    /// let mut toks = "\n abc".into_tokens();
    ///
    /// assert_eq!(toks.line_ending(), Some("\n"));
    /// assert_eq!(toks.remaining(), " abc");
    ///
    /// let mut toks = "abc".into_tokens();
    ///
    /// assert_eq!(toks.line_ending(), None);
    /// assert_eq!(toks.remaining(), "abc");
    /// ```
    fn line_ending(&mut self) -> Option<&'static str> {
        self.optional(|t| t.token('\n').then_some("\n"))
            .or_else(|| self.optional(|t| t.tokens("\r\n".chars()).then_some("\r\n")))
    }

    /// If the next tokens are a valid floating point number, then consume
    /// them and return them as an [`f64`]. Else, don't consume anything and
    /// return `None`.
    ///
    /// Like [`Tokens::parse`], the generic parameter indicates the type of buffer that
    /// may be used to collect tokens prior to parsing. Implementations like
    /// [`crate::types::StrTokens`] have optimisations to avoid needing this buffer in
    /// many cases.
    ///
    /// Use [`CharTokens::float`] if you want to consume the tokens but don't want to parse
    /// them into an f32 or f64.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, CharTokens};
    ///
    /// let mut toks = "3.14 hi".into_tokens();
    ///
    /// let n = toks.parse_f64::<String>().unwrap();
    /// assert_eq!(toks.remaining(), " hi");
    /// ```
    fn parse_f64<B>(&mut self) -> Option<f64>
    where
        B: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
    {
        parse_f::<_, f64, B, _>(self)
    }

    /// If the next tokens are a valid floating point number, then consume
    /// them and return them as an [`f32`]. Else, don't consume anything and
    /// return `None`.
    ///
    /// Like [`Tokens::parse`], the generic parameter indicates the type of buffer that
    /// may be used to collect tokens prior to parsing. Implementations like
    /// [`crate::types::StrTokens`] have optimisations to avoid needing this buffer in
    /// many cases.
    ///
    /// Use [`CharTokens::float`] if you want to consume the tokens but don't want to parse
    /// them into an f32 or f64.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, CharTokens};
    ///
    /// let mut toks = "3.14 hi".into_tokens();
    ///
    /// let n = toks.parse_f32::<String>().unwrap();
    /// assert_eq!(toks.remaining(), " hi");
    /// ```
    fn parse_f32<B>(&mut self) -> Option<f32>
    where
        B: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
    {
        parse_f::<_, f32, B, _>(self)
    }

    /// If the next tokens represent a base10 float that would be successfully parsed with
    /// `s.parse::<f32>()` or `s.parse::<f64>()`, then they will be consumed and `true` returned.
    /// Otherwise, `false` is returned and nothing is consumed.
    ///
    /// Strings such as these will be consumed:
    ///
    /// * '3.14'
    /// * '-3.14'
    /// * '2.5E10', or equivalently, '2.5e10'
    /// * '2.5E-10'
    /// * '5.'
    /// * '.5', or, equivalently, '0.5'
    /// * 'inf', '-inf', '+infinity', 'NaN'
    ///
    /// Note that alphabetical characters are not case-sensitive.
    ///
    /// More specifically, all strings that adhere to the following EBNF grammar when
    /// lowercased will be consumed, and `true` returned:
    ///
    /// ```txt
    /// Float  ::= Sign? ( 'inf' | 'infinity' | 'nan' | Number )
    /// Number ::= ( Digit+ |
    ///              Digit+ '.' Digit* |
    ///              Digit* '.' Digit+ ) Exp?
    /// Exp    ::= 'e' Sign? Digit+
    /// Sign   ::= [+-]
    /// Digit  ::= [0-9]
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, CharTokens};
    /// use core::str::FromStr;
    ///
    /// // These will all be fully consumed as valid floats:
    /// let valid_numbers = [
    ///     "3.14",
    ///     "-3.14",
    ///     "2.5E10",
    ///     "2.5e10",
    ///     "+3.123e12",
    ///     "5.",
    ///     ".5",
    ///     "+.5",
    ///     "0.5",
    ///     "inf",
    ///     "NaN",
    ///     "-infinity",
    ///     "+infinity",
    ///     "INFINITY",
    /// ];
    ///
    /// for n in valid_numbers {
    ///     let mut toks = n.into_tokens();
    ///
    ///     assert!(toks.float(), "failed to parse: {}", n);
    ///     assert_eq!(toks.remaining(), "");
    ///
    ///     n.parse::<f64>().expect("Rust can parse the string, too");
    /// }
    ///
    /// // These are all invalid and won't be consumed:
    /// let invalid_numbers = [
    ///     // Spaces aren't consumed:
    ///     " 3.14",
    ///     // Need a number one side of a decimal point:
    ///     ".",
    ///     // The "e" won't be consumed, since nothing follows it:
    ///     "3e"
    /// ];
    ///
    /// for n in invalid_numbers {
    ///     let mut toks = n.into_tokens();
    ///
    ///     assert!(!toks.float(), "succeeded in parsing: {}", n);
    ///     assert!(toks.remaining().len() > 0);
    ///
    ///     n.parse::<f64>().unwrap_err();
    /// }
    /// ```
    fn float(&mut self) -> bool {
        fn sign(t: &mut impl Tokens<Item = char>) -> bool {
            t.token('+') || t.token('-')
        }
        fn number_with_exp(t: &mut impl Tokens<Item = char>) -> bool {
            t.optional(|t| {
                if !number(t) {
                    return false;
                }
                if t.case_insensitive_eq("e") {
                    sign(t);
                    if !digits(t) {
                        return false;
                    }
                }
                true
            })
        }
        fn number(t: &mut impl Tokens<Item = char>) -> bool {
            t.optional(|t| {
                let d1 = digits(t);
                let point = t.token('.');
                if point {
                    let d2 = digits(t);
                    // If there's a point, we're happy as long as d1 or d2
                    // actually contain some digits:
                    d1 || d2
                } else {
                    // If there's no point then d1 needs to contain digits:
                    d1
                }
            })
        }
        fn digits(t: &mut impl Tokens<Item = char>) -> bool {
            t.skip_while(|c| c.is_ascii_digit()) > 0
        }

        sign(self);
        crate::one_of!(t from self;
            t.case_insensitive_eq("infinity"),
            t.case_insensitive_eq("inf"),
            t.case_insensitive_eq("nan"),
            number_with_exp(t)
        )
    }

    /// If the next tokens are equal (case insensitive) to the string provided,
    /// this returns `true` and consumes the tokens. Else, it returns `false` and
    /// doesn't consume anything.
    ///
    /// # Example
    ///
    /// ```
    /// use yap::{Tokens, IntoTokens, CharTokens};
    ///
    /// let mut toks = "HeLlO".into_tokens();
    ///
    /// assert_eq!(toks.case_insensitive_eq("hello"), true);
    /// assert_eq!(toks.remaining(), "");
    ///
    /// let mut toks = "Howdy".into_tokens();
    ///
    /// assert_eq!(toks.case_insensitive_eq("hello"), false);
    /// assert_eq!(toks.remaining(), "Howdy");
    /// ```
    fn case_insensitive_eq(&mut self, s: &str) -> bool {
        let start_loc = self.location();
        for c1 in s.chars() {
            match self.next() {
                Some(c2) => {
                    // Lowercase the chars and compare the iters for eqaality:
                    let mut c1_lower = c1.to_lowercase();
                    let mut c2_lower = c2.to_lowercase();
                    loop {
                        match (c1_lower.next(), c2_lower.next()) {
                            (Some(a), Some(b)) if a == b => continue,
                            (None, None) => break,
                            _ => {
                                self.set_location(start_loc);
                                return false;
                            }
                        }
                    }
                }
                _ => {
                    self.set_location(start_loc);
                    return false;
                }
            }
        }
        true
    }
}

impl<T: Tokens<Item = char>> CharTokens for T {}

#[inline(always)]
fn parse_f<T: Tokens<Item = char>, F, B, E>(t: &mut T) -> Option<F>
where
    T: Tokens<Item = char>,
    F: core::str::FromStr<Err = E>,
    E: core::fmt::Debug,
    B: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
{
    let l1 = t.location();
    if !CharTokens::float(t) {
        return None;
    }
    let l2 = t.location();

    let f = t
        .slice(l1, l2)
        .parse::<F, B>()
        .expect("valid float expected");

    Some(f)
}
