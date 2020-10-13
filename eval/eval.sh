#!/bin/bash

trap "trap - SIGTERM && kill -- -$$" SIGINT SIGTERM

function run_test {
    echo "_______________________________________________________________________________"
    echo "Evaluating file "$1" ..."
    /usr/bin/time -f "Max memory used (KB): %M" stack exec pomc -- "$1"
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
