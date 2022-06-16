# Change Log

Notable changes to the project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/) and the
project adheres to the [Haskell Package Versioning
Policy (PVP)](https://pvp.haskell.org)

## [unreleased]

## [1.0.0.1] - 2022-06-16

### Changed

- Stack configuration files have been created for Stackage LTS version with GHC 8.6 up to 9.2
- Dependency version requirements have been widened to allow the versions from these Stackage sets.
- In order to support GHC 9.2, `Nat` is now imported from `GHC.Typelits` instead of `GHC.Base`

## [1.0.0.0] - 2022-06-08

This is the initial release of the library.

### Added

- The POSable class, which captures non-recursive Haskell 98 data types as a product-of-sums
- A generic implementation of the POSable class, based on the generics-sop library
- A usage example (in examples/Examples.hs)
- Instances of POSable for data types in the Prelude (Bool, Maybe, Either, Ord, tuples up to length 16)

[unreleased]:   https://github.com/Riscky/posable/compare/v1.0.0.1...HEAD
[1.0.0.1]:      https://github.com/Riscky/posable/compare/v1.0.0.0...v1.0.0.1
[1.0.0.0]:      https://github.com/Riscky/posable/compare/c81f50a2b...v1.0.0.0
