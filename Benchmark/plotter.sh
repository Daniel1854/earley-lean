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

python plotter.py --mode grammar_naive --grammar 1
python plotter.py --mode grammar_naive --grammar 2
python plotter.py --mode grammar_naive --grammar 3
python plotter.py --mode grammar_naive --grammar 4
python plotter.py --mode grammar_naive --grammar 5

python plotter.py --mode grammar_opt --grammar 1
python plotter.py --mode grammar_opt --grammar 2
python plotter.py --mode grammar_opt --grammar 3
python plotter.py --mode grammar_opt --grammar 4
python plotter.py --mode grammar_opt --grammar 5

# Comparison plot of the grammars for lean
python plotter.py --mode comp

# Comparison plot of the binsizes for each grammar
python plotter.py --mode sizes

popd > /dev/null
