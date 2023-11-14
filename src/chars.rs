//! Helper functions for working with `Tokens<Item=char>`.

use crate::Tokens;

/// Parses a line ending of either `\n` (like on linux)  or `\r\n` (like on windows).
/// Returns a static string equal to the line ending parsed, or `None` if no line
/// ending is seen at this location.
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
/// ```
pub fn line_ending<T: Tokens<Item = char>>(t: &mut T) -> Option<&'static str> {
    t.optional(|t| t.token('\n').then_some("\n"))
        .or_else(|| t.optional(|t| t.tokens("\r\n".chars()).then_some("\r\n")))
}
