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

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

lemma eqLength_of_updateBinAux_of_mem (xs : List (BinItem T N)) (y : BinItem T N)
    (hNoDup : (items xs).Nodup) (hmem : y.item ∈ items xs) :
    (updateBinAux xs y).length = xs.length := by
  induction xs generalizing y with
  | nil => grind
  | cons x xs ih => grind

lemma updateBinAux_of_Red_of_eqItem (xs : List (BinItem T N)) (y : BinItem T N) {i j : Nat}
    (hNoDup : (items xs).Nodup) {yP : List ReductionPointer} (hy : y.pointer = Pointer.reduction yP)
    (hi : i < xs.length) (hx : xs[i].pointer = Pointer.null ∨ xs[i].pointer = Pointer.predecessor j)
    (heq : y.item = xs[i].item) : updateBinAux xs y = xs := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

lemma updateBinAux_of_Red_of_neqItemAux (xs : List (BinItem T N)) (y : BinItem T N) (i : Nat)
    (hi : i < xs.length) (hneq : y.item ≠ xs[i].item) (hlen : i < (updateBinAux xs y).length) :
    (updateBinAux xs y)[i] = xs[i] := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

lemma updateBinAux_of_Red_of_neqItem (xs : List (BinItem T N)) (y : BinItem T N) (i j : Nat)
    (hNoDup : (items xs).Nodup) (hi : i < xs.length) (heq : y.item = xs[i].item) (hneq : i ≠ j)
    (hj : j < xs.length) (hlen : j < (updateBinAux xs y).length) :
    (updateBinAux xs y)[j] = xs[j] := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih =>
    have : y.item ≠ (x :: xs)[j].item := by
      grind [List.nodup_iff_getElem?_ne_getElem?]
    grind [updateBinAux_of_Red_of_neqItemAux]

-- TODO: this is unused, but I can see it being useful hm
theorem updateBinAux_of_updRed (xs xs' : List (BinItem T N)) (y : BinItem T N) (i : Nat)
    (hNoDup : (items xs).Nodup) {xP yP : List ReductionPointer}
    (hi : i < xs.length) (hx : xs[i].pointer = Pointer.reduction xP) (heq : y.item = xs[i].item)
    (hy : y.pointer = Pointer.reduction yP) (hxs' : xs' = updateBinAux xs y) :
    xs'.length = xs.length ∧ ((hlen : xs'.length = xs.length) →
    xs'[i].pointer = Pointer.reduction (xP.append yP) ∧
    (∀ j, (hj : j < xs'.length ∧ i ≠ j) → xs'[j] = xs[j]'(by grind))) := by
  induction xs generalizing i y xs' with
  | nil => grind
  | cons x xs ih =>
    refine ⟨by grind [eqLength_of_updateBinAux_of_mem], ?_⟩
    intro hlen
    simp only [hxs', ne_eq, forall_and_index]
    constructor
    · if h : x.item = y.item then
        clear ih
        simp only [updateBinAux, beq_iff_eq, List.append_eq]
        have hxP : x.pointer = Pointer.reduction xP := by grind
        have hx2 : x = ⟨x.item, Pointer.reduction xP⟩ := by rw [← hxP]
        have hy2 : y = ⟨x.item, Pointer.reduction yP⟩ := by rw [← hy]; rw [h]
        grind
      else
        have hi : i - 1 < xs.length := by grind
        specialize ih (updateBinAux xs y) y (i-1) (by grind [List.Nodup.of_cons]) hi
        have xs1 : xs[i - 1].pointer = Pointer.reduction xP := by grind
        have h2 : y.item = xs[i - 1].item := by grind
        specialize ih xs1 h2 hy (by simp)
        have ⟨h3, _⟩ := ih.right ih.left
        grind
    · intro j hk hneq
      have := updateBinAux_of_Red_of_neqItem (x::xs) y i j
      grind

section Soundness

/--
Given the existance of a parse tree for a word, the word can be generated from the grammar.
-/
public theorem soundnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (w.map Symbol.terminal)) (heps : isEpsilonFree G)
    (ht : ∃ t, parse Gₗ w = some t) : G.Generates (w.map Symbol.terminal) := by
  simp only [parse, Option.dite_none_left_eq_some] at ht
  rcases ht with ⟨t, hnEmpty, ht⟩
  split at ht
  · grind
  · rename_i x idx bins hf
    apply soundnessEarleyList w h hw heps
    simp only [recognizeList, decide_eq_true_eq]
    use x
    let finalBin := (earleyList Gₗ w).bins[w.length]
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial (List.map Symbol.terminal w) x.item
    have hmem : (x, idx) ∈ (filterWithIdx finalBin P) := by grind
    have := P_of_filterWithIdx finalBin P hmem
    have := getElem_of_filterWithIdx finalBin P hmem
    grind

end Soundness

section Completeness

/--
A call to buildTree for well-formed bins never returns none.
TODO: this should be quite close to the termination argument?
-/
lemma someNode_of_buildTree_partialFixpoint (G : ContextFreeGrammarList T N) (w : List T)
    (j k : Nat) {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hk : k < w.length + 1) (hj : j < bins[k].length) (hw : w ≠ []) :
    ∃ d ts, buildTree G w hw bins hbins k hk j hj = some (Tree.node d ts) := by
  apply buildTree.partial_correctness G w hw bins hbins
    (motive := fun k hk j hj t =>
     ∃ d ts, buildTree G w hw bins hbins k hk j hj = some (Tree.node d ts))
  · intro f g k hk j hj t hwhat
    sorry
  · sorry
  · sorry

/--
A call to buildTree for well-formed bins never returns none.
TODO: this should be quite close to the termination argument?
-/
lemma someNode_of_buildTree (G : ContextFreeGrammarList T N) (w : List T) (j k : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hk : k < w.length + 1) (hj : j < bins[k].length) (hw : w ≠ []) :
    ∃ d ts, buildTree G w hw bins hbins k hk j hj = some (Tree.node d ts) := by
  unfold buildTree
  simp only [List.append_eq, Option.bind_eq_bind]
  split
  · grind
  · rename_i i heq
    -- this is required for termination, and has to be handled through isWellFormedPointers
    -- predecessor can only exist through scan, and k gets incremented
    have : 0 < k := by sorry
    have := someNode_of_buildTree G w i (k-1) hbins
    grind
  · rename_i ps heq
    -- this is an unfortunate side effect of not having pointers as
    -- ReductionPointer → List ReductionPointer
    have : ps ≠ [] := by sorry
      --let t ← buildTree G w hw bins inv endIdxA (by grind) i (by grind)
    sorry

lemma some_of_buildTree (G : ContextFreeGrammarList T N) (w : List T) (j : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hj : j < bins[w.length].length) (hw : w ≠ []) :
    ∃ t, buildTree G w hw bins hbins w.length (by grind) j hj = some t := by
  have := someNode_of_buildTree G w j w.length hbins (by grind) (by grind) hw
  rcases this with ⟨d, ts, h⟩
  use Tree.node d ts

/--
Given a word can be generated from the grammar, then there also exists a parse tree for that word.
-/
public theorem completenessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (w.map Symbol.terminal)) (heps : isEpsilonFree G)
    (hgen : G.Generates (w.map Symbol.terminal)) : ∃ t, parse Gₗ w = some t := by
  have hnEmpty : w ≠ [] := by
    have := nonEmptyDerives_of_isEpsilonFree G heps
    grind [Generates]
  have := completenessEarleyList w h hw heps hgen
  simp only [recognizeList, decide_eq_true_eq] at this
  simp only [parse, hnEmpty, ↓reduceDIte]
  split
  · rename_i heq
    rcases this with ⟨x,hx⟩
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial (List.map Symbol.terminal w) x.item
    have : x  ∈ (filterWithIdx (earleyList Gₗ w).bins[w.length] P).map Prod.fst := by
      have := memFilterWithIdx_of_mem P hx.left hx.right
      grind
    grind
  · rename_i x idx bins hf
    apply some_of_buildTree Gₗ w idx

end Completeness

/--
The correctness criteria for the parser:
A word can be generated from the grammar iff there exists a parse tree for that word.
-/
public theorem correctnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (w.map Symbol.terminal)) (heps : isEpsilonFree G) :
    G.Generates (w.map Symbol.terminal) ↔ ∃ t, parse Gₗ w = some t := by
  grind [soundnessParse, completenessParse]

end Parser
end Proofs
end Earley
