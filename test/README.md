# POMC Tests

The tests are managed by [Tasty](https://hackage.haskell.org/package/tasty), so please refer to its documentation for more usage information.

The tests have been divided in two sets:
- *Normal Tests*, which can be executed in a few minutes, and
- *Slow Tests*, which may require an exceptional amount of time and memory to be executed.

## Normal tests

To execute normal tests with the Haskell Stack, type:
```sh
stack test --ta '-p "Normal Tests"'
```

If you want to execute only, e.g., test 42 from the group "SAS MiniProc MC Eval Tests", type:
```sh
stack test --ta '-p "/Normal Tests/&&/SAS MiniProc MC Eval Tests/&&/42/"'
```

You may as well execute tests with 8 threads:
```sh
stack test --ta '-p "Normal Tests" +RTS -N8 -RTS'
```

## Slow tests

To execute slow tests with the Haskell Stack, type:
```sh
stack test --ta '-p "Slow Tests"'
```

You may want to impose a timeout when running these:
```sh
stack test --ta '-p "Slow Tests" --timeout=2h'
```

## Tips

- To display proper stack traces when exceptions are thrown, run tests with `--profile` and `+RTS -xc -RTS`.

- To run tests in `ghci` for debugging, you may do as follows:
```sh
$ stack ghci pomc:test-pomc
ghci> import Test.Tasty
ghci> import TestMC
ghci> import System.Environment
ghci> setEnv "TASTY_PATTERN" "PATTERN"
ghci> :trace defaultMain TestMC.tests
...
```

# Benchmarks

Some tests have also been packaged as benchmarks with the [Tasty.Bench](https://hackage.haskell.org/package/tasty-bench) framework,
with the main purpose of measuring performance optimizations.

You may run them with
```sh
stack bench --ba '-p "PATTERN"'
```
where `PATTERN` is any Tasty pattern, and all arguments supported by `test` can also be used.
