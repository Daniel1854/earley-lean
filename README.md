# Lean Earley Parser
An Earley Parser Formalization as part of my master thesis.
Following the work from Rau et al (<https://doi.org/10.4230/LIPIcs.ITP.2024.31>).

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
- [ ] Recognizer
  - [ ] Implement
  - [ ] Refinement Correctness Proof
- [ ] Parser
  - [ ] Implementation
  - [ ] Correctness Proof
- [ ] Evaluation/Benchmark
- [ ] Performance Improvements?

Possible improvements upon the results of Rau depending on my pace:
- worst-case O(n^3), caching stuff/improving accesses through some indexed datastructures?
- compute multiple parse trees (meh, is that useful? how would you combat cyclic grammars?)
- handle epsilon derivations
- more exciting proofs about the parse tree?

## Benchmark
Benchmark:
- main taking a grammar (deserializing some json?) and a textfile?
- script which takes a grammar and produces some text: random, min, max paths
  - worst for non-cached and also cached version
  - there are also very simple grammars
- which other parser to compare with?

Example Languages:
- Classic CFG: Dyck Language/the language of all properly matched parentheses
```
S → SS | (S) | ε
```
- ambiguous `O(n^3)`:
```
S -> SS | a
```
- unambiguous `O(n^2)` (but also regular):
```
S -> aS | a
```
- Bounded state, non-right rec `O(n)`:
```
S -> Sa | a
```
