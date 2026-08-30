/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Slice
public import Earley.Derivation
public import Earley.Proofs.Finiteness
public import Earley.Recognizer
public import Earley.Proofs.Recognizer
public import Earley.CachedRecognizerPointers
public import Earley.Proofs.CachedRecognizerPointers
public import Earley.Parser

/-!
This module houses the correctness proofs for the
  _____
 |  __ \
 | |__) |_ _ _ __ ___  ___ _ __
 |  ___/ _` | '__/ __|/ _ \ '__|
 | |  | (_| | |  \__ \  __/ |
 |_|   \__,_|_|  |___/\___|_|


The proofs follow the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Proofs
namespace Parser

section Naive

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Recognizer
open Earley.Proofs.Recognizer
open Earley.Parser
open Utils
open ContextFreeGrammar

variable {T N : Type} [BEq T] [LawfulBEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

section Soundness

/--
Given the existance of a parse tree for a word, the word can be generated from the grammar.
-/
public theorem soundnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (ht : ∃ t, parse Gₗ w = some t) : G.Generates (mapT w) := by
  simp only [parse, Option.dite_none_left_eq_some] at ht
  rcases ht with ⟨t, hnEmpty, ht⟩
  split at ht
  · simp at ht
  · rename_i x idx bins hf
    apply soundnessEarleyList w h
    simp only [recognizeList, decide_eq_true_eq]
    use x.item
    let finalBin := (earleyList Gₗ w).bins[w.size]
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial w.size x.item
    have hmem : (x, idx) ∈ (filterWithIdx finalBin P) := by grind
    have := P_of_filterWithIdx finalBin P hmem
    have := getElem_of_filterWithIdx finalBin P hmem
    grind

end Soundness

section Completeness

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
/--
A call to buildTree for well-formed bins never returns none or even a Tree.leaf.
This follows the structure of buildTree quite closely, and the same termination argument holds.
-/
lemma someNode_of_buildTree (G : ContextFreeGrammarList T N) (w : Array T) (j k : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (hk : k < w.size + 1) (hj : j < bins[k].length)
    (hw : w ≠ #[]) : ∃ d ts, buildTree G w hw bins hbins hwf k hk j hj = some (Tree.node d ts) := by
  unfold buildTree
  simp only [List.append_eq, Option.bind_eq_bind]
  split
  · use Symbol.nonterminal bins[k][j].item.rule.input
    use []
  · rename_i i heq
    have := someNode_of_buildTree G w i (k-1) hbins
    grind [wfPointerAux_of_predPointer]
  · rename_i endIdxA pi pj _ heq
    have := wfPointerAux_of_redPointer hwf _ _ heq
    have := someNode_of_buildTree G w pi endIdxA hbins hwf (by lia) (by lia) hw
    rcases this with ⟨d,ts,ht⟩
    have := someNode_of_buildTree G w pj k hbins hwf (by lia) (by lia) hw
    grind
-- If we go away from the two-dimensional view of the bins to a one-dimensional one,
-- then each recursive call accesses a smaller index of the bin.
termination_by ((bins.toList.map List.length).take k).foldl Add.add 0 + j
decreasing_by
  · rename Nat => i
    rename_i heq
    have := wfPointerAux_of_predPointer hwf _ _ heq
    have : k ≠ 0 := by
      grind [wfPointerAux_of_predPointer]
    have : ((bins.toList.map List.length).take (k - 1)).foldl Add.add 0 + bins[k-1].length =
        ((bins.toList.map List.length).take k).foldl Add.add 0 := by
      have := foldl_add_nth bins.toList 0 (k-1) (by grind)
      grind
    lia
  · rename_i endIdxA pi pj _ _ _ _
    have : endIdxA < k ∨ (endIdxA = k ∧ pi < j) := by grind [wfPointerAux_of_redPointer]
    rcases this with h | h
    · have : ((bins.toList.map List.length).take endIdxA).foldl Add.add 0 + bins[endIdxA].length ≤
             ((bins.toList.map List.length).take k).foldl Add.add 0 := by
        have := foldl_le_of_le (bins.toList.map List.length) 0 k endIdxA (by grind)
        grind
      lia
    · lia
  · rename Nat => pj
    have : pj < j := by grind [wfPointerAux_of_redPointer]
    simp [this]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma some_of_buildTree (G : ContextFreeGrammarList T N) (w : Array T) (j : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (hj : j < bins[w.size].length) (hw : w ≠ #[]) :
    ∃ t, buildTree G w hw bins hbins hwf w.size (by simp) j hj = some t := by
  have := someNode_of_buildTree G w j w.size hbins hwf (by simp) (by lia) hw
  rcases this with ⟨d, ts, h⟩
  use Tree.node d ts

/--
Given a word can be generated from the grammar, then there also exists a parse tree for that word.
-/
public theorem completenessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) (hgen : G.Generates (mapT w)) :
    ∃ t, parse Gₗ w = some t := by
  have hnEmpty : w ≠ #[] := by
    have := nonEmptyDerives_of_isEpsilonFree heps
    grind [Generates]
  have := completenessEarleyList w h heps hgen
  simp only [recognizeList, decide_eq_true_eq] at this
  simp only [parse, hnEmpty, ↓reduceDIte]
  split
  · rename_i heq
    rcases this with ⟨x,hx⟩
    let P := fun y : EarleyItem T G.NT => isFinished Gₗ.initial w.size y
    grind [notP_of_emptyFilterWithIdx]
  · rename_i x idx bins hf
    apply some_of_buildTree Gₗ w idx

end Completeness

/--
The correctness criteria for the parser:
A word can be generated from the grammar iff there exists a parse tree for that word.
-/
public theorem correctnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) :
    G.Generates (mapT w) ↔ ∃ t, parse Gₗ w = some t := by
  grind [soundnessParse, completenessParse]

end Naive

section Cached

open Earley.Model
open Earley.Recognizer
open Earley.CachedRecognizerPointers
open Earley.Proofs.CachedRecognizerPointers
open Earley.Parser
open Utils

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)]

public theorem parseCached_eq_parse {G : ContextFreeGrammarList T N} (w : Array T) :
    parseCached G w = parse G w := by
  simp only [parseCached, parse]
  have : rawList (earleyCached G w).bins = (earleyList G w).bins := by
    grind [earleyCachedBins_eq_earleyListBins]
  grind

/--
A refinement proof for the the same algorithm, but utilizing a cached implementation
to compute the bins.
-/
public theorem correctnessCachedParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] [Hashable G.NT] [Hashable (EarleyItem T G.NT)] (w : Array T)
    {Gₗ : ContextFreeGrammarList T G.NT} (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) :
    G.Generates (mapT w) ↔ ∃ t, parseCached Gₗ w = some t := by
  grind [parseCached_eq_parse, correctnessParse]

end Cached

end Parser
end Proofs
end Earley
