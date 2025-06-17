# Changelog

## v3.0.0 (TBD)

- Add POPACheck
- Support for probabilistic pushdown model checking
- Support for MiniProb inputs (MiniProc + probabilistic assignments and observations)

## v2.2.0 (2024/08/02)

- Add SMT-based model checking engine (only for finite-word model checking)
- MiniProc expressions can now be embedded in POTL formulas as atomic propositions
- Better logging infrastructure
- Bug fixes and performance improvements
- More tests and benchmarks


## v2.1.0 (2023/03/08)

- MiniProc now supports fixed-width integer variables and arrays
- MiniProc now supports non-deterministic variable assignments
- MiniProc functions now support local variables
- MiniProc functions now support passing arguments by value and value-result
- Better command-line arguments parsing
- Bugfixes and performance improvements
- More tests and benchmarks


## v2.0.0 (2021/12/15)

- Support for infinite (or omega) word POTL model checking
- Better documentation
- Bug fixes and performance improvements


## v1.0.1 (2021/07/09)

- MiniProc now supports module names
- Documentation improved


## v1.0.0 (2021/03/25)

- Added MiniProc language for easily modelling procedural programs
- Output partial counterexample traces
- Added documentation sources
- Refactoring and performance optimizations


## v0.2.0 (2021/02/18)

- Other files can now be included in `.pomc` input files
- Support for POTLv1 has been removed
- Several memory and performance optimizations
