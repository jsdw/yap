/*!
This small, zero-dependency crate helps you to parse input strings and slices by building on the [`Iterator`]
interface.

The aim of this crate is to provide the sorts of functions you'd come to expect from a parser
combinator library, but without immersing you into a world of parser combinators and forcing you
to use a novel return type, library-provided errors or parser-combinator based control flow. we
sacrifice some conciseness in exchange for simplicity.

**Some specific features/goals:**
- Great documentation, with examples for almost every function provided.
- Prioritise simplicity at the cost of verbosity.
- Be iterator-centric. Where applicable, combinators return things which implement [`Tokens`]/[`Iterator`].
- Allow user defined errors to be returned anywhere that it might make sense. Some functions have `_err`
  variants incase you need error information when they don't otherwise hand back errors for simplicity.
- Location information should always be available, so that you can tell users where something went wrong.
  see [`Tokens::offset`] and [`Tokens::location()`].
- Backtracking by default. Coming from Haskell's Parsec, this feels like the sensible default. It means that
  if one of the provided parsing functions fails to parse something, it won't consume any input trying.
- Expose all of the "low level" functions. You can save and rewind to locations as needed (see [`Tokens::location`]),
  and implement any of the provided functions using these primitives.
- Aims to be "fairly quick". Avoids allocations (and allows you to do the same via the iterator-centric interface)
  almost everywhere. If you need "as fast as you can get", there amay be quicker alternatives.

Have a look at the [`Tokens`] trait for all of the parsing methods made available, and examples for each.

Have a look in the `examples` folder for more in depth examples.

# Example

```rust
use yap::{
    // This trait has all of the parsing methods on it:
    Tokens,
    // Allows you to use `.into_tokens()` on strings and slices,
    // to get an instance of the above:
    IntoTokens
};

// Step 1: convert our input into something implementing `Tokens`
// ================================================================

let mut tokens = "10 + 2 x 12-4,foobar".into_tokens();

// Step 2: Parse some things from our tokens
// =========================================

#[derive(PartialEq,Debug)]
enum Op { Plus, Minus, Multiply }
#[derive(PartialEq,Debug)]
enum OpOrDigit { Op(Op), Digit(u32) }

// The `Tokens` trait builds on `Iterator`, so we get a `next` method.
fn parse_op(t: &mut impl Tokens<Item=char>) -> Option<Op> {
    match t.next()? {
        '-' => Some(Op::Minus),
        '+' => Some(Op::Plus),
        'x' => Some(Op::Multiply),
        _ => None
    }
}

// We also get other useful functions..
fn parse_digits(t: &mut impl Tokens<Item=char>) -> Option<u32> {
    t.take_while(|c| c.is_digit(10))
     .parse::<u32, String>()
     .ok()
}

// As well as combinator functions like `sep_by_all` and `surrounded_by`..
let op_or_digit = tokens.sep_by_all(
    |t| t.surrounded_by(
        |t| parse_digits(t).map(OpOrDigit::Digit),
        |t| { t.skip_while(|c| c.is_ascii_whitespace()); }
    ),
    |t| parse_op(t).map(OpOrDigit::Op)
);

// Now we've parsed our input into OpOrDigits, let's calculate the result..
let mut current_op = Op::Plus;
let mut current_digit = 0;
for d in op_or_digit.into_iter() {
    match d {
        OpOrDigit::Op(op) => {
            current_op = op
        },
        OpOrDigit::Digit(n) => {
            match current_op {
                Op::Plus => { current_digit += n },
                Op::Minus => { current_digit -= n },
                Op::Multiply => { current_digit *= n },
            }
        },
    }
}
assert_eq!(current_digit, 140);

// Step 3: do whatever you like with the rest of the input!
// ========================================================

// This is available on the concrete type that strings
// are converted into (rather than on the `Tokens` trait):
let remaining = tokens.remaining();

assert_eq!(remaining, ",foobar");
```
*/
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

mod tokens;

#[doc(hidden)]
pub mod one_of;

pub mod chars;
pub mod types;
pub use tokens::{IntoTokens, TokenLocation, Tokens};
