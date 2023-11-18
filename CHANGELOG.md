## 0.12.0

From [#13](https://github.com/jsdw/yap/pull/13):

- Add `Tokens::parse` method, which attempt to parse the remaining tokens into some type via
  `FromStr` (and `str::parse`). This requires a buffer type (often `String`) to be provided as
  the second generic arg, and may use this to buffer tokens prior to parsing if necessary.
- Add some helper functions which allow `Tokens::parse` to be optimised in cases like `StrToken`,
  so that eg calling `toks.slice(from, to).parse::<u16,String>` for `StrTokens` and similar won't
  allocate.
- Add `Tokens::take` for taking `n` tokens (can be useful in conjunction with `parse`, above).
- Add `Tokens::eof`, `Tokens::collect` and `Tokens::consume` for finding an EOF (`None`), collecting
  tokens and consuming all tokens.
- Add `Tokens::into_iter`, for when you need to work around lifetime issues with `Tokens::as_iter`.
- Rename `Tokens::tokens_while` to `Tokens::take_while`, and `Tokens::skip_tokens_while` to
  `Tokens::skip_while`; we no longer have to worry about conflicts with `Iterator` methods.
- `Tokens::{surrounded, optional, optional_err}` now accept an `FnOnce` instead of an `FnMut`,
  allowing a little more flexibility in what is given.
- Anything which returned something implementing `Iterator` now returns something implementing
  `Tokens` instead (you can still call `.as_iter()` to then get a standard `Iterator` from this).

A shoutout to @EasyOakland for their contributions in this!

From [#13](https://github.com/jsdw/yap/pull/14):

- Add `yap::chars` module which contains some helper functions (like `parse_f64`)
  specific to `impl Tokens<Item=char>`.
- Generalise `yap::one_of!` and `Tokens::optional`; the output from expressions passed to
  either of these can now be `Option<T>` or `bool`, or more specifically anything implementing
  `yap::one_of::IsMatch`.

## 0.11.0

Thankyou @Easyoakland for both of these contributions!

- Add support for `no_std` environments ([#7](https://github.com/jsdw/yap/pull/7)).
- Add `yap::types::IterToken`, which can be used for parsing tokens from arbitrary
  iterators (as long as they impl Clone).

## 0.10.0

- Remove pointless `skip_optional` function.

## 0.9.1

- Tidy up some docs and deny missing docs on public items.

## 0.9.0

- Remove the `Iterator` supertrait requirement from `Tokens`, and instead require implementing those
  methods directly on `Tokens`. Add a `Tokens::as_iter()` method to return an Iterator from our Tokens.
  This is done to keep the Iterator interface and methods in a separate namespace from the Tokens ones.

## 0.8.1

- Fix a bug whereby `.tokens("foo")` will return true if we run out of input before completing the match.

## 0.8.0

- Add `optional_err` parser, which is like `optional` but allows any error to be propagated.

## 0.7.2

- Fix clippy warnings on `one_of` macro invocations.
- Run clippy on the codebase and add it to the CI.