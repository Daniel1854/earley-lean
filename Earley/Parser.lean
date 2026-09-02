/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Recognizer
public import Earley.Proofs.Recognizer
public import Earley.Filter
public import Earley.CachedRecognizerPointers
public import Earley.Proofs.CachedRecognizerPointers

/-!
This module represents a functional implementation of the Earley algorithm on the production of
a parse tree from bins after recognizing a word. See `Recognizer.lean` for more details on the bins.

The implementation and its proofs follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Parser

section Wellformed

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Recognizer
open Earley.Proofs.Recognizer
open Earley.Utils

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

/--
If an `EarleyItem` stems from a prediction,
then the indices have to match and the position has to be zero.
-/
@[grind]
public def predicts (x : EarleyItem T N) : Prop :=
  x.startIdx = x.endIdx ∧ x.position = 0

/--
If an `EarleyItem` stems from a scan,
then there has to be an origin item with an appropriate next symbol it got incremented from.
-/
@[grind]
public def scans (w : Array T) (x y : EarleyItem T N) (k : Nat) (h : k - 1 < w.size) : Prop :=
  y = incItem x k ∧ (∃ a, nextSymbol x = some (Symbol.terminal a) ∧ w[k-1] = a)

/--
If an `EarleyItem` stems from a complete,
then there have to be origin items with an appropriate next symbol.

TODO: y is the new item
before I used z as the original item
-/
@[grind]
public def completes (x y z : EarleyItem T N) (k : Nat) : Prop :=
  y = incItem x k
  ∧ isComplete z ∧ z.startIdx = x.endIdx
  ∧ (∃ A, nextSymbol x = some (Symbol.nonterminal A) ∧ A = z.rule.input)

public def Pointer.NullWF (entry : BinItem T N) : Prop :=
  entry.pointer = Pointer.null → predicts entry.item

public def Pointer.PreWF {w : Array T} (bins : EarleyBins T N (w.size + 1)) (entry : BinItem T N)
    (k : Nat) : Prop :=
  ∀ i, entry.pointer = Pointer.predecessor i → k ≠ 0 ∧ k - 1 < w.size
    ∧ ((hk : k - 1 < w.size) → i < bins[k-1].length
      ∧ i < bins[k - 1].length
      ∧ ((hi : i < bins[k - 1].length) → scans w bins[k-1][i].item entry.item k hk))

-- Rau does define it for all elements
public def Pointer.RedWF {w : Array T} (bins : EarleyBins T N (w.size + 1)) (entry : BinItem T N)
    (k : Nat) : Prop :=
  ∀ p ps, entry.pointer = Pointer.reduction p ps → k ≤ w.size ∧ p.endIdxA ≤ w.size
    ∧ ((h : p.endIdxA ≤ w.size) → p.i < bins[p.endIdxA].length)
    ∧ ((h : k ≤ w.size) → p.j < bins[k].length)
    ∧ ((h1 : p.endIdxA ≤ w.size) → (h2 :p.i < bins[p.endIdxA].length)
      → (h3 : k ≤ w.size) → (h4 : p.j < bins[k].length)
      → completes bins[p.endIdxA][p.i].item entry.item bins[k][p.j].item k)

/--
A pointer is well-formed with respect to an EarleyBins, if the pointer points to a stored bin item
and its corresponding item upholds invariants about the way it got created.
`k` is the index of the bin, at which the pointer is stored at.

Since reduction pointers can point towards any earlier bin than k, this is a very global property
and difficult to reason about locally. This makes it too inconvenient to merge it with
the soundness property about pointers.

We store the invariant about how the item of the pointer got created here
since it isn't relevant to the recogner proofs.
-/
@[grind]
public def Pointer.WF {w : Array T} (bins : EarleyBins T N (w.size + 1)) (entry : BinItem T N)
    (k : Nat) : Prop :=
  Pointer.NullWF entry ∧ Pointer.PreWF bins entry k ∧ Pointer.RedWF bins entry k

@[grind]
public def BinPointers.WF {w : Array T} (bins : EarleyBins T N (w.size + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → ∀ x ∈ bins[k], Pointer.WF bins x k

/--
A pointer is called sound, if the reduction pointer points towards an earlier item.
Interestingly enough, we only reason about the first pointer
since it is the only one used for buildTree anyway.
There are problematic details when merging reduction pointers since the item could in theory
skip ahead of the item that triggered the .complete operation.
-/
@[grind]
public def Pointer.isSound (pointer : Pointer) (k j : Nat) : Prop :=
  match pointer with
  | .null | .predecessor _ => True
  | .reduction p _ => (p.endIdxA < k ∨ (p.endIdxA = k ∧ p.i < j)) ∧ p.j < j

@[grind]
public def BinPointers.isSound {w : Array T} (bins : EarleyBins T N (w.size + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → ∀ j, (hj : j < bins[k].length)
    → Pointer.isSound bins[k][j].pointer k j

/--
EarleyBins is well-formed w.r.t to their pointers, if all of its bins got well-formed pointers.
-/
@[grind]
public def EarleyBins.PointerWF {w : Array T} (bins : EarleyBins T N (w.size + 1)) : Prop :=
  BinPointers.WF bins ∧ BinPointers.isSound bins

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
@[grind →]
lemma predicts_of_null {w : Array T} {bins : EarleyBins T N (w.size + 1)}
    (hwf : EarleyBins.PointerWF bins) {k : Nat} (hk : k < bins.size)
    {j : Nat} (hj : j < bins[k].length)
    (hp : bins[k][j].pointer = Pointer.null) :
    predicts bins[k][j].item := by
  have : bins[k][j] ∈ bins[k] := by grind
  grind [Pointer.NullWF]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
@[grind →]
lemma scans_of_pre {w : Array T} {bins : EarleyBins T N (w.size + 1)}
    (hwf : EarleyBins.PointerWF bins) {i j k : Nat} (hk : k < bins.size)
    (hk' : k - 1 < w.size) (hi : i < bins[k - 1].length)
    (hj : j < bins[k].length) (hp : bins[k][j].pointer = Pointer.predecessor i) :
    scans w bins[k-1][i].item bins[k][j].item k hk' := by
  have : bins[k][j] ∈ bins[k] := by grind
  grind [Pointer.PreWF]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
@[grind →]
lemma completes_of_red {w : Array T} {bins : EarleyBins T N (w.size + 1)}
    (hwf : EarleyBins.PointerWF bins) {k : Nat} (hk : k < bins.size)
    {j : Nat} (hj : j < bins[k].length) {p : ReductionPointer} {ps : List ReductionPointer}
    (hp : bins[k][j].pointer = Pointer.reduction p ps)
    (h1 : p.endIdxA ≤ w.size) (h2 : p.i < bins[p.endIdxA].length)
    (h3 : p.j < bins[k].length) :
    completes bins[p.endIdxA][p.i].item bins[k][j].item bins[k][p.j].item k := by
  have : bins[k][j] ∈ bins[k] := by grind
  grind [Pointer.RedWF]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma preWF_of_pre {w : Array T} {bins : EarleyBins T N (w.size + 1)}
    (hwf : EarleyBins.PointerWF bins) {i k : Nat} (hk : k < bins.size)
    {j : Nat} (hj : j < bins[k].length)
    (hp : bins[k][j].pointer = Pointer.predecessor i) :
    k ≠ 0 ∧ k - 1 < w.size ∧ ((hk : k - 1 < w.size) → i < bins[k-1].length) := by
  have : bins[k][j] ∈ bins[k] := by grind
  grind [Pointer.PreWF]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma redWF_of_red {w : Array T} {bins : EarleyBins T N (w.size + 1)}
    (hwf : EarleyBins.PointerWF bins) {k : Nat} (hk : k < bins.size)
    {j : Nat} (hj : j < bins[k].length) {p : ReductionPointer} {ps : List ReductionPointer}
    (hp : bins[k][j].pointer = Pointer.reduction p ps) :
    p.endIdxA ≤ w.size
      ∧ p.j < bins[k].length
      ∧ ((h : p.endIdxA ≤ w.size) → p.i < bins[p.endIdxA].length)
      ∧ (p.endIdxA < k ∨ (p.endIdxA = k ∧ p.i < j)) ∧ p.j < j := by
  have : bins[k][j] ∈ bins[k] := by grind
  grind [Pointer.RedWF]

@[grind →]
lemma updateBinAux_of_nullPre (xs : BinItems T N) (y : BinItem T N) {i : Nat}
    (hmem : y.item ∈ items xs) (hy : y.pointer = .null ∨ y.pointer = .predecessor i) :
    updateBinAux y xs = xs := by
  induction xs generalizing y with
  | nil => grind
  | cons head tail ih => grind

lemma eqLength_of_updateBinAux_of_mem (xs : BinItems T N) (y : BinItem T N)
    (hNoDup : (items xs).Nodup) (hmem : y.item ∈ items xs) :
    (updateBinAux y xs).length = xs.length := by
  induction xs generalizing y with
  | nil => grind
  | cons x xs ih => grind

lemma updateBinAux_of_Red_of_neqItemAux (xs : BinItems T N) (y : BinItem T N) (i : Nat)
    (hi : i < xs.length) (hneq : y.item ≠ xs[i].item) (hlen : i < (updateBinAux y xs).length) :
    (updateBinAux y xs)[i] = xs[i] := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

lemma updateBinAux_of_Red_of_neqItem (xs : BinItems T N) (y : BinItem T N) (i j : Nat)
    (hNoDup : (items xs).Nodup) (hi : i < xs.length) (heq : y.item = xs[i].item) (hneq : i ≠ j)
    (hj : j < xs.length) (hlen : j < (updateBinAux y xs).length) :
    (updateBinAux y xs)[j] = xs[j] := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih =>
    have : y.item ≠ (x :: xs)[j].item := by
      grind [List.nodup_iff_getElem?_ne_getElem?]
    grind [updateBinAux_of_Red_of_neqItemAux]

lemma updateBinAux_of_updRed (xs xs' : BinItems T N) (y : BinItem T N) (i : Nat)
    (hNoDup : (items xs).Nodup) {xp yp : ReductionPointer} {xP yP : List ReductionPointer}
    (hi : i < xs.length) (hx : xs[i].pointer = Pointer.reduction xp xP) (heq : y.item = xs[i].item)
    (hy : y.pointer = .reduction yp yP) (hxs' : xs' = updateBinAux y xs) :
    xs'.length = xs.length ∧ ((hlen : xs'.length = xs.length) →
    xs'[i].pointer = .reduction xp (yp::yP.append xP) ∧
    (∀ j, (hj : j < xs'.length ∧ i ≠ j) → xs'[j] = xs[j]'(by lia))) := by
  induction xs generalizing i y xs' with
  | nil => grind
  | cons x xs ih =>
    refine ⟨by grind [eqLength_of_updateBinAux_of_mem], ?_⟩
    intro hlen
    simp only [hxs', ne_eq, forall_and_index]
    constructor
    · grind
    · intro j hk hneq
      have := updateBinAux_of_Red_of_neqItem (x::xs) y i j
      grind

lemma updateBinAux_of_Red_of_eqItem (xs : BinItems T N) (y : BinItem T N) (i j : Nat)
    (hNoDup : (items xs).Nodup) (hi : i < xs.length)
    (hx : xs[i].pointer = .null ∨ xs[i].pointer = .predecessor j) (heq : y.item = xs[i].item) :
    updateBinAux y xs = xs := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

lemma wfBinPointers_of_updateBinAux' {w : Array T} {k : Nat} (bins : EarleyBins T N (w.size + 1))
    (hwfbin : BinPointers.WF bins) (hk : k < bins.size) (x : BinItem T N)
    (hbins : (items bins[k]).Nodup) (hwfy : Pointer.WF bins x k) :
    BinPointers.WF (Vector.modify bins k (fun bin => (updateBinAux x bin))) := by
  let bins' := (Vector.modify bins k (fun bin => (updateBinAux x bin)))
  intro idx hidx y hmemy
  have hmemy' : y ∈ bins'[idx] := by grind
  simp only [BinPointers.WF, Order.lt_add_one_iff] at hwfbin
  by_cases heq : k = idx
  · sorry
    --simp only [Pointer.WF, ne_eq, and_self_left]
    --specialize hwfbin k' (by lia)
  · refine ⟨by grind, ?_, ?_⟩
    · grind [updateBinAux_getElem_of_lower_idx, length_le_lengthUpdateBinAux, Pointer.PreWF]
    · grind [updateBinAux_getElem_of_lower_idx, length_le_lengthUpdateBinAux, Pointer.RedWF]

lemma soundPointers_of_updateBinAux (wlen : Nat) {k : Nat} (bins : EarleyBins T N (wlen + 1))
    (hbins : ∀ k, (hk : k ≤ wlen) → (items bins[k]).Nodup ∧ ∀ j, (hj : j < bins[k].length)
      → Pointer.isSound bins[k][j].pointer k j)
    (y : BinItem T N) (hk : k < wlen + 1) (hwf : Pointer.isSound y.pointer k bins[k].length) :
    ∀ j, (hj : j < (updateBinAux y bins[k]).length) →
    Pointer.isSound (updateBinAux y bins[k])[j].pointer k j := by
  have : y.item ∉ items bins[k] ∨
        (y.item ∈ items bins[k] ∧ ∃ i, y.pointer = .null ∨ y.pointer = .predecessor i) ∨
        (y.item ∈ items bins[k] ∧ ¬ ∃ i, y.pointer = .null ∨ y.pointer = .predecessor i) := by
    simp only [not_exists, not_or]
    grind
  rcases this with hnmem | ⟨hmem, hex⟩ | ⟨hmem, hnex⟩
  · grind
  · rcases hex with ⟨i,hi⟩
    grind
  · simp only [not_exists, not_or] at hnex
    match hy : y.pointer with
    | .null | .predecessor i => grind [hnex 0]
    | .reduction yp yP =>
      have := List.getElem_of_mem hmem
      rcases this with ⟨j', hjI', heq⟩
      have hj' : j' < bins[k].length := by grind
      match hb : bins[k][j'].pointer with
      | .null =>
        have := (hbins k (by grind)).left
        have heq' : y.item = bins[k][j'].item := by
          simp only [items, List.getElem_map] at heq
          simp [heq]
        have := updateBinAux_of_Red_of_eqItem bins[k] y j' 0 this (by grind) (by simp [hb]) heq'
        grind
      | .predecessor i =>
        have := (hbins k (by grind)).left
        have heq' : y.item = bins[k][j'].item := by
          simp only [items, List.getElem_map] at heq
          simp [heq]
        have := updateBinAux_of_Red_of_eqItem bins[k] y j' i this (by grind) (by simp [hb]) heq'
        grind
      | .reduction bp bP =>
        have hnDup := (hbins k (by grind)).left
        have : y.item = bins[k][j'].item := by grind
        have hupdRed := updateBinAux_of_updRed bins[k] (updateBinAux y bins[k]) y j' hnDup hj'
            hb this hy (by simp)
        grind

-- I cannot really simplify the goal and make the proof easier for me
-- since any item of ys can get merged into the bins and thus the `< j` would get problematic.
lemma soundPointers_of_updateBin (wlen : Nat) (k : Nat) (bins : EarleyBins T N (wlen + 1))
    (hbins : ∀ k, (hk : k ≤ wlen) → (items bins[k]).Nodup ∧ ∀ j, (hj : j < bins[k].length)
      → Pointer.isSound bins[k][j].pointer k j)
    (ys : BinItems T N) (hk : k < wlen + 1)
    (hwf : ∀ y ∈ ys, Pointer.isSound y.pointer k bins[k].length) :
    ∀ j, (hj : j < (updateBin bins[k] ys).length) →
    Pointer.isSound (updateBin bins[k] ys)[j].pointer k j := by
  induction ys generalizing bins with
  | nil => grind
  | cons y ys ih =>
    intro j hj
    let bins' := Vector.set bins k (updateBinAux y bins[k]) hk
    have hSaux := soundPointers_of_updateBinAux wlen bins hbins y hk (by grind)
    have : ∀ y ∈ ys, Pointer.isSound y.pointer k bins'[k].length := by
      clear ih
      simp only [Pointer.isSound]
      grind [length_le_lengthUpdateBinAux]
    have hbins' : (∀ (k : ℕ) (hk : k ≤ wlen), (items bins'[k]).Nodup ∧
        ∀ (j : ℕ) (hj : j < bins'[k].length), Pointer.isSound bins'[k][j].pointer k j) := by
      clear this
      intro k2 hk2
      constructor
      · grind [noDup_of_updateBinAux bins[k] y]
      · grind
    specialize ih bins' hbins' (by grind)
    grind

theorem pointerWF_of_updateBin (G : ContextFreeGrammarList T N) (w : Array T) {k : Nat}
    (bins : EarleyBins T N (w.size + 1)) (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins)
    (ys : BinItems T N) (hk : k < w.size + 1)
    (hwfPy : ∀ y ∈ ys, Pointer.WF bins y k)
    (hwfSy : ∀ y ∈ ys, Pointer.isSound y.pointer k bins[k].length) :
    EarleyBins.PointerWF (updateBins bins k ys)  := by
  induction ys generalizing bins k with
  | nil =>
    have : Vector.modify bins k (fun x => x) = bins := by grind
    grind
  | cons y ys ih =>
    simp [updateBins, EarleyBins.PointerWF]
    --refine ⟨by grind [soundPointers_of_updateBinAux, wfBinPointers_of_updateBinAux]
    sorry

    --· have ⟨h0,h1,h2,h3⟩ := hwf k (by lia)
    --  simp only [heq]
    --  have hwfb : BinPointers.WF bins (updateBins bins k ys)[k] k := by
    --    have := wfBinPointers_of_updateBin w bins bins[k] h2 ys (by grind)
    --    grind
    --  have : ∀ (i : ℕ) (hi : i ≤ w.size), bins[i].length
    --      ≤ (updateBins bins k ys)[i].length := by grind [lengthNth_le_lengthUpdateBinNth]
    --  have := wfBinPointers_of_updatedBins w bins (updateBins bins k ys) hk this hwfb
    --  grind
    --· intro j hj
    --  have := soundPointers_of_updateBin w.size k bins (by grind) ys
    --  grind

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_scanList {w : Array T} (j k : Nat) {a : T} {bins : EarleyBins T N (w.size + 1)}
    (x : EarleyItem T N) (hk : k < w.size) (hj : ¬ (j ≥ bins[k].length)) :
    ∀ y ∈ (scanList w x a k hk j), Pointer.WF bins y (k+1) := by
  intro y hmem
  refine ⟨?_, ?_, ?_⟩
  · grind [scanList, Pointer.NullWF]
  · simp only [Pointer.PreWF, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, add_tsub_cancel_right, and_self_left, true_and]
    intro j' y'
    refine ⟨by grind, ?_⟩
    intro hk
    refine ⟨by grind [scanList], ?_⟩
    intro hi
    simp [scans]
    sorry
  · grind [scanList, Pointer.RedWF]

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_scanList {w : Array T} (j k : Nat) {a : T}
    {bins : EarleyBins T N (w.size + 1)} (x : EarleyItem T N) (hk : k < w.size) :
    ∀ y ∈ scanList w x a k hk j, Pointer.isSound y.pointer (k+1) bins[k+1].length := by
  grind [scanList]

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_predictList (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (A : N) {bins : EarleyBins T N (w.size + 1)} :
    ∀ x ∈ (predictList G A k), Pointer.WF bins x k := by
  grind [predictList, Pointer.NullWF, Pointer.PreWF, Pointer.RedWF]

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_predictList (G : ContextFreeGrammarList T N) (wlen k : Nat) (A : N)
    (bins : EarleyBins T N (wlen + 1)) (hk : k < wlen + 1) :
    ∀ x ∈ predictList G A k, Pointer.isSound x.pointer k bins[k].length := by
  grind [predictList]

omit [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_completeList {G : ContextFreeGrammarList T N} (w : Array T) (j k : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins) (y : EarleyItem T N)
    (hk : k < bins.size) (hmemy : y ∈ (items bins[k])) (hj : j < bins[k].length) :
    ∀ x ∈ (completeList y bins (by grind) j), Pointer.WF bins x k := by
  intro x hmemx
  simp only [completeList, List.mem_map, Prod.exists] at hmemx
  let P := fun x : BinItem T N => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)
  let originBin := bins[y.startIdx]'(by grind)
  let filteredOriginBin := filterWithIdx originBin P
  simp only [Pointer.WF, Pointer.NullWF, Pointer.PreWF, Pointer.RedWF]
  refine ⟨by grind, by grind, ?_⟩
  -- z is the original item, which will be completed
  rcases hmemx with ⟨z,zIdx,⟨hmemz,hx⟩⟩
  have xP : x.pointer = Pointer.reduction ⟨y.startIdx, zIdx, j⟩ [] := by grind
  simp only [xP]
  intro p ps hps
  refine ⟨by lia, by grind, ?_, by grind, ?_⟩
  · intro hbounds
    have : y.startIdx < w.size + 1 := by grind
    exact filterWithIdx_le_length bins[p.endIdxA]
      (fun x => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)) p.i (by grind)
  · intro h1 h2 h3 h4
    sorry

omit [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_completeList {G : ContextFreeGrammarList T N} (w : Array T) (j k : Nat)
    (bins : EarleyBins T N (w.size + 1)) (hbins : EarleyBins.WF G bins) (y : EarleyItem T N)
    (hk : k < bins.size) (hmemy : y ∈ (items bins[k])) (hj : j < bins[k].length) :
    ∀ x ∈ completeList y bins (by grind) j, Pointer.isSound x.pointer k bins[k].length := by
  simp only [Pointer.isSound]
  intro x hmemx
  simp only [completeList, List.mem_map, Prod.exists] at hmemx
  let P := fun x : BinItem T N => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)
  let originBin := bins[y.startIdx]'(by grind)
  let filteredOriginBin := filterWithIdx originBin P
  -- z is the original item, which will be completed
  rcases hmemx with ⟨z,zIdx,⟨hmemz,hx⟩⟩
  have xP : x.pointer = Pointer.reduction ⟨y.startIdx, zIdx, j⟩ [] := by grind
  simp only [xP]
  refine ⟨?_, by grind⟩
  simp only [EarleyBins.WF, Order.lt_add_one_iff] at hbins
  have : y.startIdx < k ∨ y.startIdx = k := by grind
  rcases this with h | h
  · grind
  · simp only [h, lt_self_iff_false, true_and, false_or, gt_iff_lt]
    exact filterWithIdx_le_length bins[k] P zIdx (by grind)

theorem pointerWF_of_earleyBinsList (G : ContextFreeGrammarList T N) (w : Array T)
    (k : Nat) (hk : k < w.size + 1) : EarleyBins.PointerWF (earleyBinsList G w k hk).bins := by
  sorry

theorem pointerWF_of_earleyList (G : ContextFreeGrammarList T N) (w : Array T) :
    EarleyBins.PointerWF (earleyList G w).bins := by
  grind [pointerWF_of_earleyBinsList]

end Wellformed

section Naive

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Recognizer
open Earley.Utils

variable {T N : Type} [BEq T] [BEq N]

/--
The basic tree data structure with no limit on its successors.
-/
inductive Tree (T N : Type) where
  /--
  A leaf with data, but no successors.
  -/
  | leaf (data : Symbol T N) : Tree T N
  /--
  A node with data and its successors.
  -/
  | node (data : Symbol T N) (succ : List (Tree T N)) : Tree T N
deriving BEq, Repr

-- This may want to live somewhere else. Some Util module with the graphviz function?
instance [ToString T] [ToString N] : ToString (Symbol T N) where
 toString sym := match sym with
   | Symbol.terminal t => toString t
   | Symbol.nonterminal nt => toString nt

mutual
  /--
  Accumulates a graphviz string for a list of trees and returns the indices of each of these.
  -/
  def toGraphvizAuxList [ToString T] [ToString N] (acc : String) (idx : Nat)
      (accChildren : List Nat) : List (Tree T N) → String × Nat × List Nat
    | [] => ⟨acc,idx,accChildren⟩
    | t::ts =>
      let ⟨acc,newIdx⟩ := toGraphvizAux acc idx t
      let accChildren := accChildren.append [idx]
      toGraphvizAuxList acc newIdx accChildren ts

  /--
  Accumulates a graphviz string for a tree.
  -/
  def toGraphvizAux [ToString T] [ToString N] (acc : String) (idx : Nat) : Tree T N → String × Nat
    | Tree.leaf d => ⟨acc ++ s!"\n  {idx} [label=\"{d}\", shape=circle];", (idx+1)⟩
    | Tree.node d ts =>
      let node := s!"\n  {idx} [label=\"{d}\", shape=circle];"
      let ⟨acc, newIdx, childIndices⟩ := toGraphvizAuxList (acc ++ node) (idx+1) [] ts
      -- Create an edge from the node to all of its direct children
      let edges := String.join (childIndices.map (fun i => s!"\n  {idx} -> {i};"))
      ⟨acc ++ edges, newIdx⟩
end

/--
Transform a tree into a graphviz compatible format.
-/
def toGraphviz [ToString T] [ToString N] (t : Tree T N) : String :=
  let ⟨graph, _⟩ := toGraphvizAux "Digraph tree {" 1 t
  graph ++ "\n}"

lemma foldl_add_nth {α : Type} (xs : List (List α)) (m k : Nat) (hk : k < xs.length) :
    ((xs.map List.length).take k).foldl Add.add m + xs[k].length =
    ((xs.map List.length).take (k+1)).foldl Add.add m := by
  induction xs generalizing m k with
  | nil => grind
  | cons x xs ih =>
    if h : k = 0 then
      simp only [h, List.map_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, zero_add,
        List.take_succ_cons, List.foldl_cons]
      lia
    else
      have := ih x.length (k-1) (by grind)
      grind

lemma acc_le_foldl (xs : List Nat) (n : Nat) : n ≤ xs.foldl Add.add n := by
  induction xs generalizing n with
  | nil => grind
  | cons head tail ih => grind

lemma foldl_le_of_le (xs : List Nat) (m k j : Nat) (hk : k < xs.length) (hjk : j < k) :
    (xs.take j).foldl Add.add m + xs[j] ≤ (xs.take k).foldl Add.add m := by
  induction xs generalizing m k j with
  | nil => grind
  | cons x xs ih =>
    if h : k = 0 then
      lia
    else if hj : j = 0 then
      simp only [hj, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      have := @List.take_succ_cons _ x xs (k-1)
      grind [acc_le_foldl]
    else
      specialize ih (m+x) (k-1) (j-1) (by grind) (by grind)
      have := @List.take_succ_cons _ x xs (k-1)
      have heq : k - 1 + 1 = k := by lia
      rw [heq] at this
      simp only [this, List.foldl_cons, ge_iff_le]
      have := @List.take_succ_cons _ x xs (j-1)
      have heq : j - 1 + 1 = j := by lia
      rw [heq] at this
      simp only [this, List.foldl_cons, ge_iff_le]
      have : j - 1 < xs.length := by grind
      have : (x::xs)[j] = xs[j-1] := by grind
      rw [this]
      apply ih

/--
Reconstruct the parse tree by searching the origin data from the EarleyBins.
-/
public def buildTree (G : ContextFreeGrammarList T N) (w : Array T) (hw : w ≠ #[])
    (bins : EarleyBins T N (w.size + 1)) (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (k : Nat) (hk : k < w.size + 1)
    (j : Nat) (hj : j < bins[k].length) : Option (Tree T N) :=
  let binItem := bins[k][j]
  match hp : binItem.pointer with
  | .null =>
    -- Start building a subtree
    some (Tree.node (Symbol.nonterminal binItem.item.rule.input) [])
  | .predecessor i => do
    -- Add subtree starting from terminal
    have : k - 1 < w.size := by grind
    let t ← buildTree G w hw bins hbins hwf (k-1) (by lia) i (by grind [preWF_of_pre])
    match t with
    | Tree.leaf d => none
    | Tree.node d ts =>
      some (Tree.node d (ts.append [Tree.leaf (Symbol.terminal w[k-1])]))
  | .reduction ⟨endIdxA,pI,pJ⟩ ps => do
    -- We simply take the first possible parse tree.
    have : bins[k][j].pointer = .reduction { endIdxA := endIdxA, i := pI, j := pJ } ps := by grind
    have := redWF_of_red hwf _ _ this
    let t ← buildTree G w hw bins hbins hwf endIdxA (by lia) pI (by lia)
    match t with
    | Tree.leaf d => none
    | Tree.node d ts => do
      let t ← buildTree G w hw bins hbins hwf k (by lia) pJ (by lia)
      some (Tree.node d (ts.append [t]))
-- Idea: if we go think of the two-dimensional bins as a continuous one-dimensional one,
-- then each recursive call accesses a smaller index of the bin.
termination_by ((bins.toList.map List.length).take k).foldl Add.add 0 + j
decreasing_by
  · have : k ≠ 0 := by grind [preWF_of_pre]
    have : ((bins.toList.map List.length).take (k - 1)).foldl Add.add 0 + bins[k-1].length =
        ((bins.toList.map List.length).take k).foldl Add.add 0 := by
      have := foldl_add_nth bins.toList 0 (k-1) (by grind)
      grind
    grind [preWF_of_pre]
  · have : endIdxA < k ∨ (endIdxA = k ∧ pI < j) := by grind
    rcases this with h | h
    · have : ((bins.toList.map List.length).take endIdxA).foldl Add.add 0 + bins[endIdxA].length ≤
             ((bins.toList.map List.length).take k).foldl Add.add 0 := by
        have := foldl_le_of_le (bins.toList.map List.length) 0 k endIdxA (by grind)
        grind
      lia
    · lia
  · rename Nat => pj
    have : pj < j := by grind
    simp [this]

/--
Tries to parse a word with given grammar, and returns a parse tree if succesful.
-/
public def parse [LawfulBEq (EarleyItem T N)] (G : ContextFreeGrammarList T N) (w : Array T) :
    Option (Tree T N) :=
  -- This could be inferred from the result of earleyList,
  -- but this is easier to reason about and performance-wise should be equal.
  if hw : w = #[] then
    none
  else
    let wfBins := earleyList G w
    -- Find the finished item, and follow its pointers.
    let P := fun x => isFinished G.initial w.size x.item
    match h : filterWithIdx wfBins.bins[w.size] P with
    | [] => none
    | (_, i)::_ =>
      have inv := pointerWF_of_earleyList G w
      have := filterWithIdx_le_length wfBins.bins[w.size] P i (by grind)
      buildTree G w hw wfBins.bins wfBins.inv inv w.size (by simp) i this

end Naive

section Cached

open Earley.Model
open Earley.Model.EarleyItem
open Earley.CachedRecognizerPointers
open Earley.Proofs.CachedRecognizerPointers
open Earley.Utils

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)]

theorem pointerWF_of_earleyCached (G : ContextFreeGrammarList T N) (w : Array T) :
    EarleyBins.PointerWF (rawList (earleyCached G w).bins) := by
  have inv := pointerWF_of_earleyList G w
  grind [earleyCachedBins_eq_earleyListBins]

public def parseCached (G : ContextFreeGrammarList T N) (w : Array T) : Option (Tree T N) :=
  -- This could be inferred from the result of earleyList,
  -- but this is easier to reason about and performance-wise should be equal.
  if hw : w = #[] then
    none
  else
    let wfBins := earleyCached G w
    let bins := rawList wfBins.bins
    -- Find the finished item, and follow its pointers.
    let P := fun x => isFinished G.initial w.size x.item
    -- One _could_ use Array.findIdx here, but the implementation isn't actually more efficient.
    match h : filterWithIdx bins[w.size] P with
    | [] => none
    | (_, i)::_ =>
      have inv := pointerWF_of_earleyCached G w
      have := filterWithIdx_le_length bins[w.size] P i (by grind)
      buildTree G w (by grind) bins wfBins.inv inv w.size (by simp) i this

end Cached
end Parser
end Earley
