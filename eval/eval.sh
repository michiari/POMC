#!/bin/bash

trap "trap - SIGTERM && kill -- -$$" SIGINT SIGTERM

if [[ "$OSTYPE" == "darwin"* ]]; then
    TME=gtime    # gnu-time is required in MacOS
else             # linux-gnu
    TME=/usr/bin/time
fi

function run_test {
    echo "_______________________________________________________________________________"
    echo "Evaluating file "$1" ..."
    "$TME" -f "Max memory used (KB): %M" stack exec pomc -- "$1" +RTS -t --machine-readable -RTS
}

if [ $# -eq 0 ]; then
    TESTS=($(find . -name "*.pomc"))
else
    TESTS=("$@")
fi

for T in "${TESTS[@]}"; do
    if [ -f $T ]; then
        run_test $T
    elif [ -d $T ]; then
        for F in $(find $T -name "*.pomc"); do
            run_test $F
        done
    fi
done
