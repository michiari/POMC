# POMC
[![Release](https://img.shields.io/github/v/release/michiari/POMC?include_prereleases)](https://github.com/michiari/POMC/releases)
[![License](https://img.shields.io/github/license/michiari/POMC)](COPYING.md)

A model-checking tool for verifying procedural programs with exceptions against POTL (Precedence Oriented Temporal Logic) specifications.
POTL is a temporal logic capable of expressing context-free specifications, particularly well-suited for verifying procedural programs with exceptions.
It can express properties such as:
- Stack inspection
- Function-local properties
- Hoare-style pre/post conditions for functions
- No-throw guarantee (for exceptions)
- Exception safety

For usage info, including input/output formats, see the [User Guide](docs/guide.pdf) and related [Publications](#publications).

## Build

POMC requires the [Z3 Theorem Prover](https://github.com/Z3Prover/z3)'s library development files to be built (package `libz3-dev` on Debian-based systems).
The current version of POMC has been tested with Z3 4.8.12.

POMC has been packaged with the [Haskell Tool Stack](https://www.haskellstack.org/).
To build it, after cloning the repository just type the following commands in a terminal:
```sh
stack setup
stack build
```
Stack will automatically download and compile all required packages.
Then, POMC can be executed on an input file `file.pomc` as follows:
```sh
stack exec -- pomc file.pomc
```

## Publications

1. Chiari, M., Mandrioli, D., Pontiggia, F., & Pradella, M. (2023). A model checker for operator precedence languages. ACM Transactions on Programming Languages and Systems, 45(3), 1-66. [doi:10.1145/3608443](https://doi.org/10.1145/3608443)
