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