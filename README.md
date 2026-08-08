# Lean Earley Parser
An Earley Parser Formalization as part of my master thesis.
Following the work from Rau et al (<https://doi.org/10.4230/LIPIcs.ITP.2024.31>).

## Graphviz
To visualize a parse tree, you can use the function `toGraphviz` on a `Tree`.
This will return a string compatible with graphviz, which you can save into a file.
See `saveTree` in `Test/Recognizer.lean` for further inspiration.

Then execute the following command on a machine with graphviz installed
```bash
dot -Tsvg tree.gv -o tree.svg
```
or the following for png:
```bash
dot -T png tree.gv -O
```
and you can look at the rendered file.

## General Plan
- [x] Setup Repository for writing thesis/presentations
- [x] Setup Repository with Mathlib+Testrunner
- [?] Establish CFG Types
  - [x] use mathlib types for now
  - [?] write a metaprogram for `EBNF String -> CFG`
- [x] Typing Judgements
  - [x] EarleyItem
  - [x] EarleySet
  - [x] Correctness Proof
- [x] Recognizer
  - [x] Implement
  - [x] Termination Proof
  - [x] Refinement Correctness Proof
- [x] Parser
  - [x] Implementation
  - [x] Graphviz
  - [x] Termination Proof
  - [x] Correctness Proof
- [x] Evaluation/Benchmark: mostly done
- [x] Performance Improvement to O(n^3)
  - [x] Implementation: Cached containment and completion version with and without Pointers
  - [x] Correctness Proof for the version with the pointers
  - [x] Cached Parser Refinement
  - [x] Partial Recognizer without pointers for perf measurements
  - [ ] Mimic Scala 100% Recognizer for perf measurements ?
