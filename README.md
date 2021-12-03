# typeof

## Dependencies

- The [Nix] package manager

Run `nix-shell` to open a shell with all the dependencies:

``` bash
nix-shell
```

## Developing

Inside `nix-shell`, run:

``` bash
cabal repl
```

## Run tests and lints

Inside `nix-shell`, run:

``` bash
cabal test
hlint .
```

## Building

Inside `nix-shell`, run:

``` bash
cabal build
```

[Nix]: https://nixos.org/


## Stack

Tested with stack 2.7.3
