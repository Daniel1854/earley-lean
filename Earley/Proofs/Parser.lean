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

TODO: Rename a ton of lemmas since I forgot about the style in the middle /o\
      https://leanprover-community.github.io/contribute/naming.html
-/

@[expose] public section

namespace Earley
namespace Proofs
namespace Parser

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Proofs.Model
open Earley.Proofs.Finiteness
open Earley.Recognizer
open Earley.Proofs.Recognizer
open Earley.Parser
open Utils
open ContextFreeRule
open ContextFreeGrammar

variable {T N : Type} [BEq T] [LawfulBEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

omit [BEq T] [BEq N] in
lemma wfPointerAux_of_predPointer {G : ContextFreeGrammarList T N} {w : List T} {i k j : Nat}
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hm : k < w.length + 1) (hn : j < bins[k].length)
    (h : bins[k][j].pointer = Pointer.predecessor i) :
    k - 1 ≤ w.length ∧ ((h : k - 1 ≤ w.length) → i < bins[k-1].length) := by
  have ⟨_, pInv, _⟩ := hbins k (by simp [hm])
  simp only [isWellFormedBinPointers, isWellFormedPointer, tsub_le_iff_right] at pInv
  specialize pInv bins[k][j] (by simp)
  grind

section Soundness

/--
Given the existance of a parse tree for a word, the word can be generated from the grammar.
-/
public theorem soundnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (ht : ∃ t, parse Gₗ w = some t) : G.Generates (mapT w) := by
  simp only [parse, Option.dite_none_left_eq_some] at ht
  rcases ht with ⟨t, hnEmpty, ht⟩
  split at ht
  · simp at ht
  · rename_i x idx bins hf
    apply soundnessEarleyList w h
    simp only [recognizeList, decide_eq_true_eq]
    use x.item
    let finalBin := (earleyList Gₗ w).bins[w.length]
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial (mapT w) x.item
    have hmem : (x, idx) ∈ (filterWithIdx finalBin P) := by grind
    have := P_of_filterWithIdx finalBin P hmem
    have := getElem_of_filterWithIdx finalBin P hmem
    grind

end Soundness

section Completeness

-- TODO: care about this.
omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
/--
A call to buildTree for well-formed bins never returns none or even a Tree.leaf.
This follows the structure of buildTree quite closely, and the same termination argument holds.
-/
lemma someNode_of_buildTree (G : ContextFreeGrammarList T N) (w : List T) (j k : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hk : k < w.length + 1) (hj : j < bins[k].length) (hw : w ≠ []) :
    ∃ d ts, buildTree G w hw bins hbins k hk j hj = some (Tree.node d ts) := by
  unfold buildTree
  simp only [List.append_eq, Option.bind_eq_bind]
  split
  · use Symbol.nonterminal bins[k][j].item.rule.input
    use []
  · rename_i i heq
    have := someNode_of_buildTree G w i (k-1) hbins
    grind
  · rename_i endIdxA pi pj _ heq
    have := wfPointerAux_of_redPointer hbins _ _ heq
    have := someNode_of_buildTree G w pi endIdxA hbins (by lia) (by lia) hw
    rcases this with ⟨d,ts,ht⟩
    have := someNode_of_buildTree G w pj k hbins (by lia) (by lia) hw
    grind
-- If we go away from the two-dimensional view of the bins to a one-dimensional one,
-- then each recursive call accesses a smaller index of the bin.
termination_by ((bins.toList.map List.length).take k).foldl Add.add 0 + j
decreasing_by
  · rename Nat => i
    have : k ≠ 0 := by grind
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
lemma some_of_buildTree (G : ContextFreeGrammarList T N) (w : List T) (j : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hj : j < bins[w.length].length) (hw : w ≠ []) :
    ∃ t, buildTree G w hw bins hbins w.length (by simp) j hj = some t := by
  have := someNode_of_buildTree G w j w.length hbins (by simp) (by lia) hw
  rcases this with ⟨d, ts, h⟩
  use Tree.node d ts

/--
Given a word can be generated from the grammar, then there also exists a parse tree for that word.
-/
public theorem completenessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (mapT w)) (heps : isEpsilonFree G)
    (hgen : G.Generates (mapT w)) : ∃ t, parse Gₗ w = some t := by
  have hnEmpty : w ≠ [] := by
    have := nonEmptyDerives_of_isEpsilonFree heps
    grind [Generates]
  have := completenessEarleyList w h hw heps hgen
  simp only [recognizeList, decide_eq_true_eq] at this
  simp only [parse, hnEmpty, ↓reduceDIte]
  split
  · rename_i heq
    rcases this with ⟨x,hx⟩
    let P := fun y : EarleyItem T G.NT => isFinished Gₗ.initial (mapT w) y
    grind [notP_of_emptyFilterWithIdx]
  · rename_i x idx bins hf
    apply some_of_buildTree Gₗ w idx

end Completeness

/--
The correctness criteria for the parser:
A word can be generated from the grammar iff there exists a parse tree for that word.
-/
public theorem correctnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (mapT w)) (heps : isEpsilonFree G) :
    G.Generates (mapT w) ↔ ∃ t, parse Gₗ w = some t := by
  grind [soundnessParse, completenessParse]

end Parser
end Proofs
end Earley
