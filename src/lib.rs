//! This crate helps you to parse input strings and slices by building on the [`Iterator`] interface.
//! 
//! The aim of this crate is to provide transparent, flexible and easy to understand parsing utilities 
//! which work on arbitrary slices and strings. Some goals of this library are:
//! 
//! - Be simple but flexible. The entire interface is visible on the [`Tokens`] trait, and everything used
//!   internally to implement those functions can be used by you, too.
//! - Do the obvious thing where possible. For this library, that generally means using backtracking
//!   functions which won't consume any input unless they successfully parse it.
//! - Make it possible to return custom error and location information anywhere you might need it.
//! - Work with standard language features by offering an iterator based interface, rather than requiring
//!   specific combinators for control flow and such.
//! 
//! Have a look at the [`Tokens`] trait for all of the parsing methods, and examples for each.
//! 
//! # Example
//! 
//! ```rust
//! use yap::{ 
//!     // This trait has all of the parsing methods on it:
//!     Tokens,
//!     // Allows you to use `.into_tokens()` on strings and slices, 
//!     // to get an instance of the above:
//!     IntoTokens
//! };
//! 
//! // Step 1: convert some tokens into something implementing `Tokens`
//! // ================================================================
//! 
//! let mut tokens = "1+2/3-4,foobar".into_tokens();
//! 
//! // Step 2: Parse some things from our tokens
//! // =========================================
//! 
//! #[derive(PartialEq,Debug)]
//! enum Op { Plus, Minus, Divide }
//! #[derive(PartialEq,Debug)]
//! enum OpOrDigit { Op(Op), Digit(u32) }
//! 
//! // The `Tokens` trait builds on `Iterator` and so looks similar,
//! // as well as having all of the normal `Iterator` methods on it.
//! fn parse_op(t: &mut impl Tokens<Item=char>) -> Option<Op> {
//!     match t.next()? {
//!         '-' => Some(Op::Minus),
//!         '+' => Some(Op::Plus),
//!         '/' => Some(Op::Divide),
//!         _ => None
//!     }
//! }
//! 
//! fn parse_digit(tokens: &mut impl Tokens<Item=char>) -> Option<u32> {
//!     let c = tokens.next()?;
//!     c.to_digit(10)
//! }
//! 
//! // Combinator functions exist which accept functions that consume tokens,
//! // and combine them. Here, we parse digits separated by operators, leaving
//! // any input that does not match this.
//! //
//! // These functions themselves tend to return iterators, so that you can 
//! // collect up the results however you choose. No input is consumed beyond 
//! // that which was successfully parsed.
//! let output: Vec<_> = tokens.sep_by_all(
//!     |t| parse_digit(t).map(OpOrDigit::Digit), 
//!     |t| parse_op(t).map(OpOrDigit::Op)
//! ).collect();
//! 
//! // Step 3: do whatever you like with the rest of the input!
//! // ========================================================
//! 
//! // This is available on the concrete type that strings
//! // are converted into (rather than on the `Tokens` trait):
//! let remaining = tokens.remaining();
//! 
//! assert_eq!(remaining, ",foobar");
//! ```

mod tokens;
mod utils;

pub mod types;
pub use tokens::{ Tokens, IntoTokens, TokenLocation };
