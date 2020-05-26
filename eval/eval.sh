#!/bin/bash

if [ $# -eq 0 ]; then
    TESTS=(./*.pomc)
else
    TESTS=("$@")
fi

for F in "${TESTS[@]}"; do
    echo "_______________________________________________________________________________"
    echo "Evaluating file "$F" ..."
    stack exec pomc -- "$F"
done
