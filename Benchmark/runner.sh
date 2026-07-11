#!/bin/bash
#
# Maybe a simple bash script is sufficient for the running portion.
#
# Example calls:
# bash runner.sh 1

set -e
GRAMMAR_INDEX=$1
REPO_ROOT=`git rev-parse --show-toplevel`

usage() {
  echo "Usage: runner.sh <GRAMMAR_INDEX>"
  echo ""
  echo "Valid values for GRAMMAR_INDEX range from 1-5:"
  echo "(1) S -> SS  | a"
  echo "(2) S -> aS  | a"
  echo "(3) S -> aSa | a"
  echo "(4) S -> Sa  | a"
  echo "(5) S -> SX  | a, X -> Y | Z, Y -> a, Z -> a"
  exit 1
}

pushd $REPO_ROOT > /dev/null

if [[ -z "${1}" ||  "${1}" -lt 1 || "${1}" -gt 5 ]]; then
  usage
fi

if [ "${GRAMMAR_INDEX}" == 1 ]; then
  INPUT_SIZES=(10 20 50 100 200 300)
elif [ "${GRAMMAR_INDEX}" == 2 ]; then
  INPUT_SIZES=(10 20 50 100 200 300 400 500 600 700 800)
elif [ "${GRAMMAR_INDEX}" == 3 ]; then
  INPUT_SIZES=(10 20 50 100 200 300 400 500 600 700 800)
elif [ "${GRAMMAR_INDEX}" == 4 ]; then
  INPUT_SIZES=(10 20 50 100 200 300 400 500 600 700 800 900 1000 2000 3000 5000 10000 15000 20000)
elif [ "${GRAMMAR_INDEX}" == 5 ]; then
  INPUT_SIZES=(10 20 50 100 200 300 400 500 600 700 800 900 1000 2000 3000 5000 10000)
fi

#echo "Building Lean Project.."
lake build Bench

# Init the .csv
LOG_FILE="Benchmark/lean/lean_grammar=${1}.csv"
echo "num_chars,num_miliseconds,num_bins,num_pointers,num_total" > $LOG_FILE
printf "Running..."
for i in "${INPUT_SIZES[@]}"; do
  printf " $i"
  # lake exe Bench $GRAMMAR_INDEX $i >> $LOG_FILE
  .lake/build/bin/Bench $GRAMMAR_INDEX $i >> $LOG_FILE
done
echo ""
echo "Done!"

popd > /dev/null
