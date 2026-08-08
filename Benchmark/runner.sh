#!/bin/bash
#
# Maybe a simple bash script is sufficient for the running portion.
#
# Example calls:
# bash runner.sh 1 default

set -e
GRAMMAR_INDEX=$1
VARIANT=$2
REPO_ROOT=`git rev-parse --show-toplevel`

usage() {
  echo "Usage: runner.sh <GRAMMAR_INDEX> <VARIANT>"
  echo ""
  echo "Valid values for GRAMMAR_INDEX range from 1-5:"
  echo "(1) S -> SS  | a"
  echo "(2) S -> aS  | a"
  echo "(3) S -> aSa | a"
  echo "(4) S -> Sa  | a"
  echo "(5) S -> SX  | a, X -> Y | Z, Y -> a, Z -> a"
  echo ""
  echo "Valid values for VARIANT are:"
  echo "'lean-naive'          | naive algorithm"
  echo "'lean-opt'            | cache for containment check and completion filtering"
  echo "'lean-item-pointers'  | cache for containment check + maintaining pointers"
  echo "'lean-opt-pointers'   | caches + maintaining pointers"
  exit 1
}

pushd $REPO_ROOT > /dev/null

if [[ -z "${GRAMMAR_INDEX}" || -z "${VARIANT}" || "${GRAMMAR_INDEX}" -lt 1 || "${GRAMMAR_INDEX}" -gt 5 ]]; then
  usage
fi

if [ "${GRAMMAR_INDEX}" == 1 ]; then
  if [ "${VARIANT}" == "lean-naive" ]; then
    INPUT_SIZES=(10 100 125 150 175 200 225 250 275 300 325 350 375 400)
  elif [ "${VARIANT}" == "lean-opt" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1500)
  elif [ "${VARIANT}" == "lean-item-pointers" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000)
  elif [ "${VARIANT}" == "lean-opt-pointers" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000)
  fi
elif [ "${GRAMMAR_INDEX}" == 2 ]; then
  if [ "${VARIANT}" == "lean-naive" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1500)
  elif [ "${VARIANT}" == "lean-opt" ]; then
    INPUT_SIZES=(10 100 1000 2000 3000 4000 5000 6000 7000 8000 9000 10000 11000 12000 13000 14000 15000)
  elif [ "${VARIANT}" == "lean-item-pointers" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1500)
  elif [ "${VARIANT}" == "lean-opt-pointers" ]; then
    INPUT_SIZES=(10 100 1000 2000 3000 3500 4000)
  fi
elif [ "${GRAMMAR_INDEX}" == 3 ]; then
  if [ "${VARIANT}" == "lean-naive" ]; then
    INPUT_SIZES=(10 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1500)
  elif [ "${VARIANT}" == "lean-opt" ]; then
    INPUT_SIZES=(10 100 1000 2000 3000 4000 5000 6000 7000 8000 9000 10000 11000 12000 13000 14000 15000)
  elif [ "${VARIANT}" == "lean-item-pointers" ]; then
    INPUT_SIZES=(10 100 500 1000 1100 1200 1300 1400 1500 1600 1750)
  elif [ "${VARIANT}" == "lean-opt-pointers" ]; then
    INPUT_SIZES=(10 100 1000 2000 3000 3500 4000)
  fi
elif [ "${GRAMMAR_INDEX}" == 4 ]; then
  if [ "${VARIANT}" == "lean-naive" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 10000000 20000000 30000000)
  elif [ "${VARIANT}" == "lean-opt" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 10000000 20000000 30000000)
  elif [ "${VARIANT}" == "lean-item-pointers" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 10000000 20000000 30000000)
  elif [ "${VARIANT}" == "lean-opt-pointers" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 10000000 20000000 30000000)
  fi
elif [ "${GRAMMAR_INDEX}" == 5 ]; then
  if [ "${VARIANT}" == "lean-naive" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 5000000 10000000)
  elif [ "${VARIANT}" == "lean-opt" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 5000000 10000000 15000000)
  elif [ "${VARIANT}" == "lean-item-pointers" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 5000000 10000000)
  elif [ "${VARIANT}" == "lean-opt-pointers" ]; then
    INPUT_SIZES=(10 100 1000 10000 100000 1000000 5000000 10000000)
  fi
fi

echo "Building Lean Project.."
lake build Bench

# Init the .csv
LOG_FILE="Benchmark/lean/lean_grammar=${GRAMMAR_INDEX}_variant=${VARIANT}.csv"
echo "num_chars,num_miliseconds,num_bins,num_pointers,num_total" > $LOG_FILE
printf "Running..."
for i in "${INPUT_SIZES[@]}"; do
  printf " $i"
  # lake exe Bench $GRAMMAR_INDEX $VARIANT $i >> $LOG_FILE
  .lake/build/bin/Bench $GRAMMAR_INDEX $VARIANT $i >> $LOG_FILE
done
echo ""
echo "Done!"

popd > /dev/null
