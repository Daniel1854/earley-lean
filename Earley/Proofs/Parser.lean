/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Finite.Prod
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Slice
public import Earley.Derivation
public import Earley.Fixpoint
public import Earley.Proofs.Fixpoint
public import Earley.Recognizer
public import Earley.Proofs.Finiteness

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
open Earley.Fixpoint
open Earley.Proofs.Fixpoint
open Earley.Recognizer
open Earley.Proofs.Finiteness
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

--/--
--The correctness criteria for the parser.
--
--A word can be generated from the grammar iff there exists a parse tree.
---/
--public theorem correctnessBuildTree {G : ContextFreeGrammar T} [BEq T] [BEq G.NT] [LawfulBEq G.NT]
--    [LawfulBEq (EarleyItem T G.NT)] (w : List T) {Gₗ : ContextFreeGrammarList T G.NT}
--    (h : CFGEqCFGₗ G Gₗ) (hw : isWord G (w.map Symbol.terminal)) :
--    G.Generates (w.map Symbol.terminal) ↔ recognizeList Gₗ w := by
--  sorry

end Parser
end Proofs
end Earley
