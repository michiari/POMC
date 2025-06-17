# OPPAS
[![Release](https://img.shields.io/github/v/release/michiari/POMC?include_prereleases)](https://github.com/michiari/POMC/releases)
[![License](https://img.shields.io/github/license/michiari/POMC)](COPYING.md)

*Operator-Precedence Program Analysis Suite*

OPPAS contains two tools: POMC and POPACheck.


## POMC 🔎

POMC is a model-checking tool for verifying procedural programs with exceptions against POTL (Precedence Oriented Temporal Logic) specifications.
POTL is a temporal logic capable of expressing context-free specifications, particularly well-suited for verifying procedural programs with exceptions.
It can express properties such as:
- Stack inspection
- Function-local properties
- Hoare-style pre/post conditions for functions
- No-throw guarantee (for exceptions)
- Exception safety


## POPACheck 🎲

POAPACheck is a model-checking tool for recursive probabilistic programs formally modelled as probabilistic Operator Precedence Automata (pOPA), a subclass of probabilistic Pushdown Automata.
POPACheck support model checking of the temporal logics LTL and a fragment of POTL.


For usage info, including input/output formats, see the [User Guide](docs/guide.pdf) and related [Publications](#publications).


## Build 🏗️

The suite has been packaged with the [Haskell Tool Stack](https://www.haskellstack.org/).

It requires development files of the following libraries
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3) (tested with versions 4.11.2, 4.14.1)
- [BLAS/LAPACK](https://www.netlib.org/lapack/)
- [GSL](https://www.gnu.org/software/gsl/)
- [GLPK](https://www.gnu.org/software/glpk/)

On most Debian-based GNU/Linux distributions (including Ubuntu), they can be installed with:
```sh
sudo apt install libz3-dev libgsl0-dev liblapack-dev libatlas-base-dev
```

To build the suite, after cloning the repository type the following commands in a terminal:
```sh
stack setup
stack build
```
Stack will automatically download and compile all required packages.
Then, POMC can be executed on an input file `file.pomc` as follows:
```sh
stack exec -- pomc file.pomc
```

And POPACheck as follows:
```sh
stack exec -- popacheck file.pomc
```

For more info, please refer to the User's Guide in `docs`.
We tested the suite mostly on Ubuntu 24.04/24.10.
Please let us know if you have issues running it on other OSes.


## Publications 📖

Main reference for the explicit-state model checker (`pomc --explicit`):

1. Chiari, M., Mandrioli, D., Pontiggia, F., & Pradella, M. (2023). A model checker for operator precedence languages. ACM Transactions on Programming Languages and Systems, 45(3), 1-66. [doi:10.1145/3608443](https://doi.org/10.1145/3608443)

Reference for the SMT-based model checker (`pomc --smt`):

2. Chiari, M., Geatti, L., Gigante, N., & Pradella, M. (2024). SMT-Based Symbolic Model-Checking for Operator Precedence Languages. CAV 2024. LNCS, 14681, 387-408. Springer, Cham. [doi:10.1007/978-3-031-65627-9_19](https://doi.org/10.1007/978-3-031-65627-9_19)

Reference for the probabilistic model checker (`popacheck`):

3. Pontiggia, F., Bartocci, E., & Chiari, M. (2025). POPACheck: a Model Checker for probabilistic Pushdown Automata. CAV 2025. LNCS, to appear. [arXiv:2502.03956](https://doi.org/10.48550/arXiv.2502.03956)
