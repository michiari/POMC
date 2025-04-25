# POPACheck
[![Release](https://img.shields.io/github/v/release/michiari/POMC?include_prereleases)](https://github.com/michiari/POMC/releases)
[![License](https://img.shields.io/github/license/michiari/POMC)](COPYING.md)

A model-checking tool for recursive probabilistic programs formally modelled as probabilistic Operator Precedence Automata (pOPA), a subclass of probabilistic Pushdown Automata. POPACheck support model checking of temporal logics LTL and a fragment of POTL.
POTL is a temporal logic capable of expressing context-free specifications, particularly well-suited for procedural/recursive programs.

## Build

POPACheck has been packaged with the [Haskell Tool Stack](https://www.haskellstack.org/).

Its dependencies are [Z3](https://microsoft.github.io/z3guide/z3) 4.8.12, [BLAS/LAPACK](https://www.netlib.org/lapack/), [GSL](https://www.gnu.org/software/gsl/), and [GLPK](https://www.gnu.org/software/glpk/).
On Unix-like systems, just install them with: 
```
$ sudo apt install libz3-dev libgsl0-dev liblapack-dev libatlas-base-dev

```
To build POPACheck, after cloning the repository just type the following commands in a terminal:
```
$ stack setup
$ stack build
```
Stack will automatically download and compile all the required packages.
Then, POPACheck can be executed on an input file `file.pomc` as follows:
```
$ stack exec -- popacheck file.pomc
```

For more info, please refer to the User's Guide in `docs`.
