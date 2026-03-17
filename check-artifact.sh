#!/usr/bin/env sh 

# This shell script runs the entire artifact

# First we check the mechanization
lake lean CompositionalProtocolProof/CompositionalMCM.lean 2>&1 | grep axioms

#Now we run the murphi scripts
echo "TODO: add murphi scripts here!"
