## 0.8.1

- Fix a bug whereby `.tokens("foo")` will return true if we run out of input before completing the match.

## 0.8.0

- Add `optional_err` parser, which is like `optional` but allows any error to be propagated.

## 0.7.2

- Fix clippy warnings on `one_of` macro invocations.
- Run clippy on the codebase and add it to the CI.