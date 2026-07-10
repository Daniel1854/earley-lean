#!/bin/bash
set -xe
REPO_ROOT=`git rev-parse --show-toplevel`
pushd $REPO_ROOT"/Benchmark" > /dev/null

# Comparison plot of each grammar for the scala-variants and lean
python plotter.py --mode grammar --grammar 1
python plotter.py --mode grammar --grammar 2
python plotter.py --mode grammar --grammar 3
python plotter.py --mode grammar --grammar 4
python plotter.py --mode grammar --grammar 5

# Comparison plot of the grammars for lean
# python plotter.py --mode comp

# TODO: Some Bar chart bin size diagram for the different grammars?
#python plotter.py --mode bar --grammar 1

popd > /dev/null
