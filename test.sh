#!/bin/sh

if [ "$1" == "--help" ]; then
    echo "USAGE ./test.sh TYPE [NUMBER]"
    echo " TYPE == a -> All tests"
    echo " TYPE == u -> Unit tests"
    echo " TYPE == q -> QuickCheck tests"
    echo
    echo " NUMBER == n -> Tell QuickCheck to generate n test cases"
    exit 0
fi

ARGS=""

if   [ "$1" == "a" ]; then ARGS=''
elif [ "$1" == "u" ]; then ARGS='-p Unit'
elif [ "$1" == "q" ]; then ARGS='-p Quick'
fi

if [ ! -z "$2" ]; then ARGS+=" --quickcheck-tests $2"; fi

rm tests.stderr && stack test --ta "$ARGS" 2>tests.stderr
