# POSable

A library to convert non-recursive Haskell-98 datatypes to a Product-of-Sums
representation - and back. This makes it possible to compactly store arrays of
sum types in a struct-of-arrays representation, which is used in array-based
languages like [Accelerate].

[Accelerate]: https://www.acceleratehs.org/

## Dependencies

- The [Stack] package manager (Tested with stack 2.7.3)
- `stylish-haskell` and `hlint` (for linting only)

[Stack]: https://docs.haskellstack.org/en/stable/README/

## Tests and lints

``` bash
stylish-haskell -r src examples test
hlint src examples test
stack test
```

## Building

``` bash
stack build
# To build the docs
stack haddock posable
```

## Examples

In the [examples] folder you will find examples that describe how to use this
library.
