# POMC
[![Release](https://img.shields.io/github/v/release/michiari/POMC?include_prereleases)](https://github.com/michiari/POMC/releases)
[![License](https://img.shields.io/github/license/michiari/POMC)](COPYING.md)

A model-checking tool for the temporal logic POTL.
POTL is a temporal logic capable of expressing context-free specifications, particularly well-suited for procedural programs.

## Build

POMC requires the [Z3 Theorem Prover](https://github.com/Z3Prover/z3)'s library development files to be built (package `libz3-dev` on Debian-based systems).
The current version of POMC has been tested with Z3 4.8.12.

POMC has been packaged with the [Haskell Tool Stack](https://www.haskellstack.org/).
To build it, after cloning the repository just type the following commands in a terminal:
```
$ stack setup
$ stack build
```
Stack will automatically download and compile all the required packages.
Then, POMC can be executed on an input file `file.pomc` as follows:
```
$ stack exec -- pomc file.pomc
```

For more info, please refer to the User's Guide in `docs`.
