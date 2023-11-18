//! Helper functions that can be used when working with `Tokens<Item=char>`.

use crate::Tokens;

/// If the next tokens are either `\n` (like on linux)  or `\r\n` (like on windows),
/// this will consume then and return `Some("\n")` or `Some("\r\n")` respectively.
/// If the next tokens are not one of these, then `None` will be returned and nothing
/// will be consumed.
///
/// # Example
///
/// ```
/// use yap::{Tokens, IntoTokens, chars};
///
/// let mut toks = "\r\n abc".into_tokens();
///
/// assert_eq!(chars::line_ending(&mut toks), Some("\r\n"));
/// assert_eq!(toks.remaining(), " abc");
///
/// let mut toks = "\n abc".into_tokens();
///
/// assert_eq!(chars::line_ending(&mut toks), Some("\n"));
/// assert_eq!(toks.remaining(), " abc");
///
/// let mut toks = "abc".into_tokens();
///
/// assert_eq!(chars::line_ending(&mut toks), None);
/// assert_eq!(toks.remaining(), "abc");
/// ```
pub fn line_ending(toks: &mut impl Tokens<Item = char>) -> Option<&'static str> {
    toks.optional(|t| t.token('\n').then_some("\n"))
        .or_else(|| toks.optional(|t| t.tokens("\r\n".chars()).then_some("\r\n")))
}

/// If the next tokens are a valid Rust floating point number (see [`float`]
/// for more details), then consume them and return them as an [`f32`]. Else,
/// don't consume anything and return `None`.
///
/// Like [`Tokens::parse`], the generic parameter `Buf` indicates the type of buffer
/// that may be used to collect tokens prior to parsing. Implementations like
/// [`crate::types::StrTokens`] are optimised to avoid using a buffer in
/// many cases.
///
/// # Example
///
/// ```
/// use yap::{Tokens, IntoTokens, chars};
///
/// let mut toks = "3.14 hi".into_tokens();
///
/// let n = chars::parse_f64::<String>(&mut toks).unwrap();
/// assert_eq!(toks.remaining(), " hi");
/// ```
pub fn parse_f64<Buf>(toks: &mut impl Tokens<Item = char>) -> Option<f64>
where
    Buf: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
{
    parse_f::<_, f64, Buf, _>(toks)
}

/// If the next tokens are a valid Rust floating point number (see [`float`]
/// for more details), then consume them and return them as an [`f32`]. Else,
/// don't consume anything and return `None`.
///
/// Like [`Tokens::parse`], the generic parameter `Buf` indicates the type of buffer
/// that may be used to collect tokens prior to parsing. Implementations like
/// [`crate::types::StrTokens`] are optimised to avoid using a buffer in
/// many cases.
///
/// # Example
///
/// ```
/// use yap::{Tokens, IntoTokens, chars};
///
/// let mut toks = "3.14 hi".into_tokens();
///
/// let n = chars::parse_f32::<String>(&mut toks).unwrap();
/// assert_eq!(toks.remaining(), " hi");
/// ```
pub fn parse_f32<Buf>(toks: &mut impl Tokens<Item = char>) -> Option<f32>
where
    Buf: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
{
    parse_f::<_, f32, Buf, _>(toks)
}

// Parse an f32 or f64 from the input, returning None if the input
// did not contain a valid rust style float. This is expected to be
// used only to parse f32s or f64s and may panic otherwise.
#[inline(always)]
fn parse_f<T: Tokens<Item = char>, F, B, E>(t: &mut T) -> Option<F>
where
    T: Tokens<Item = char>,
    F: core::str::FromStr<Err = E>,
    E: core::fmt::Debug,
    B: core::iter::FromIterator<char> + core::ops::Deref<Target = str>,
{
    let l1 = t.location();
    if !float(t) {
        return None;
    }
    let l2 = t.location();

    let f = t
        .slice(l1, l2)
        .parse::<F, B>()
        .expect("valid float expected");

    Some(f)
}

/// If the next tokens represent a base10 float that would be successfully parsed with
/// `s.parse::<f32>()` or `s.parse::<f64>()`, then they will be consumed and `true` returned.
/// Otherwise, `false` is returned and nothing is consumed.
///
/// Rust float parsing is quite permissive in general. Strings such as these will be treated
/// as valid floats and fully consumed:
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
/// use yap::{Tokens, IntoTokens, chars};
/// use core::str::FromStr;
///
/// // These will all be fully consumed as valid floats:
/// let valid_numbers = [
///     "3.14",
///     "-3.14",
///     "2.5E10",
///     "2.5e-10",
///     "2.5e+10",
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
///     assert!(chars::float(&mut toks), "failed to parse: {}", n);
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
///     assert!(!chars::float(&mut toks), "succeeded in parsing: {}", n);
///     assert!(toks.remaining().len() > 0);
///
///     n.parse::<f64>().unwrap_err();
/// }
/// ```
pub fn float(toks: &mut impl Tokens<Item = char>) -> bool {
    fn sign(t: &mut impl Tokens<Item = char>) -> bool {
        t.token('+') || t.token('-')
    }
    fn number_with_exp(t: &mut impl Tokens<Item = char>) -> bool {
        t.optional(|t| {
            if !number(t) {
                return false;
            }
            if case_insensitive_eq(t, "e") {
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

    sign(toks);
    crate::one_of!(t from toks;
        case_insensitive_eq(t, "infinity"),
        case_insensitive_eq(t, "inf"),
        case_insensitive_eq(t, "nan"),
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
/// use yap::{Tokens, IntoTokens, chars};
///
/// let mut toks = "HeLlO".into_tokens();
///
/// assert_eq!(chars::case_insensitive_eq(&mut toks, "hello"), true);
/// assert_eq!(toks.remaining(), "");
///
/// let mut toks = "Howdy".into_tokens();
///
/// assert_eq!(chars::case_insensitive_eq(&mut toks, "hello"), false);
/// assert_eq!(toks.remaining(), "Howdy");
/// ```
pub fn case_insensitive_eq(toks: &mut impl Tokens<Item = char>, s: &str) -> bool {
    let start_loc = toks.location();
    for c1 in s.chars() {
        match toks.next() {
            Some(c2) => {
                // Lowercase the chars and compare the iters for eqaality:
                let mut c1_lower = c1.to_lowercase();
                let mut c2_lower = c2.to_lowercase();
                loop {
                    match (c1_lower.next(), c2_lower.next()) {
                        (Some(a), Some(b)) if a == b => continue,
                        (None, None) => break,
                        _ => {
                            toks.set_location(start_loc);
                            return false;
                        }
                    }
                }
            }
            _ => {
                toks.set_location(start_loc);
                return false;
            }
        }
    }
    true
}
