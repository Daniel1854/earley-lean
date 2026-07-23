/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Filter
public import Earley.Proofs.Finiteness
public import Mathlib.Data.Set.Card

/-!
This module represents a computable implementation of the Earley algorithm.

Given an input word `w = a_0 .. a_(n-1)` of length `n`, we maintain a list of `n+1` bins `B_k`.
For the initial starting position and position after parsing a certain characters,
we maintain a bin of the possible states we could be in.
Each bin contains a set of `BinItem`s, which are a pair of an `EarleyItem` and a `Pointer`,
which help us keep track of its origin. The pointer is only required to assemble the parse tree.

The `endIdx` of an `EarleyItem` corresponds always to the bin number.
`B_0` is filled with the items from the INIT rule.

The parse tree will only be built _after_ a word has been fully recognized,
thus the Recognizer has to keep track of all its bins until its done.

The algorithm goes through the bins in ascending order.
Due to a complication with epsilon rules, `.complete` may miss transitions,
so Rau only reasons about epsilon free grammars.

The implementation and its proofs follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Recognizer

open Model
open EarleyItem
open Utils

/--
A pointer, which encapsulates the relevant origin data for a completion operation.
This requires only three indices since the endIdx of the completed item is the same as the item,
that this reduction pointer belongs to.
- Bins Index for the original Item and its index with that bin
- The index of the completed item within the current bin

Example:
A → α • B β, startIdxA, endIdxA stored in bins[endIdxA][i]
B → γ •,     startIdxB, endIdxB stored in bins[endIdxB][j]
-/
public structure ReductionPointer where
  /-- `endIdx` of the original item. -/
  endIdxA : Nat
  /-- Index of the original item within its bin. -/
  i : Nat
  /-- Index of the completed item within its bin. -/
  j : Nat
deriving BEq, Repr

/--
A Pointer helps keep track of the origin of an EarleyItem.
These are only required to assemble the parse tree after the successful recognition.
-/
inductive Pointer where
  /-- .init/.predict: no origin data needed. -/
  | null : Pointer
  /-- .scan: origin index for previous bin. -/
  | predecessor (i : Nat) : Pointer
  /-- .complete: nonempty list of possible reduction pointers -/
  | reduction (p : ReductionPointer) (ps : List ReductionPointer) : Pointer
deriving BEq, Repr

/--
The items of a bin. It contains the EarleyItem and data for its origin.
-/
public structure BinItem (T N : Type) where
  /-- The EarleyItem of the item. -/
  item : EarleyItem T N
  /-- The origin data of the item. -/
  pointer : Pointer
deriving BEq, Repr

abbrev BinItems (T N : Type) : Type :=
  List (BinItem T N)

/--
Abbreviation for a two-dimensional list.
Outer list corresponds to the different positions for the word,
inner list corresponds to the items of that specific position.
-/
abbrev EarleyBins (T N : Type) (n : Nat) : Type :=
  Vector (BinItems T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

@[grind]
def items (bin : BinItems T N) : List (EarleyItem T N) :=
  bin.map (fun x => x.item)

section WellFormedBin

/--
The items of an EarleyBin are well-formed, if
- there are no duplicate items in the bin
- all items in the bin are well-formed
- the endIdx of all items match the index of the bin
-/
@[grind]
public def BinItems.WF {L : Type} (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (bin : L) [Membership (BinItem T N) L] : Prop :=
  ∀ x ∈ bin, isWellFormed G.rules w.length x.item ∧ x.item.endIdx = k

/--
A pointer is well-formed with respect to an EarleyBins, if TODO
TODO: Since the pointers require access to previous bins, it's a bit inconvenient to merge.
      I could make BinPointers.WF reason about the index and simply merge?
      But the proofs get quite a bit more involved then.
-/
@[grind]
public def Pointer.WF (w : List T) (bins : EarleyBins T N (w.length + 1))
    (pointer : Pointer) (k : Nat) : Prop :=
  match pointer with
  | .null => True
  | .predecessor i => k ≠ 0 ∧ k - 1 ≤ w.length ∧ ((h : k - 1 ≤ w.length) → i < bins[k-1].length)
  | .reduction p ps => k ≤ w.length ∧ p.endIdxA ≤ w.length ∧
      ((h : p.endIdxA ≤ w.length) → p.i < bins[p.endIdxA].length) ∧
      ((h : k ≤ w.length) → p.j < bins[k].length)

@[grind]
public def BinPointers.WF (w : List T) (bins : EarleyBins T N (w.length + 1))
    (bin : BinItems T N) (k : Nat) : Prop :=
  ∀ x ∈ bin, Pointer.WF w bins x.pointer k

/--
Interestingly enough, we only reason about the first pointer
since it is the only one used for buildTree anyway.
There are problematic details when merging reduction pointers.
-/
@[grind]
public def Pointer.isSound (pointer : Pointer) (k j : Nat) : Prop :=
  match pointer with
  | .null | .predecessor _ => True
  | .reduction p _ => (p.endIdxA < k ∨ (p.endIdxA = k ∧ p.i < j)) ∧ p.j < j

/--
EarleyBins are well-formed, if all of its bins are well-formed.
-/
@[grind]
public def EarleyBins.WF (G : ContextFreeGrammarList T N) (w : List T)
    (bins : EarleyBins T N (w.length + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → (items bins[k]).Nodup ∧ BinItems.WF G w k bins[k]
    ∧ BinPointers.WF w bins bins[k] k
    ∧ ∀ j, (hj : j < bins[k].length) → Pointer.isSound bins[k][j].pointer k j

/--
A combination of an EarleyBins with a well-formedness Invariant about it.
-/
public structure WfEarleyBins (G : ContextFreeGrammarList T N) (w : List T) where
  bins : EarleyBins T N (w.length + 1)
  inv : EarleyBins.WF G w bins

/--
List-based implementation of the .init operation.
Returns a list filled with all possible .init states.
-/
public def initList (G : ContextFreeGrammarList T N) : BinItems T N :=
  let rules := G.rules.filter (fun r => r.input == G.initial)
  rules.map (fun r => ⟨⟨r,0,0,0⟩, Pointer.null⟩)

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
TODO: Returning an Option would be more sensible since appending to a linked list is expensive?
      But I want to be close to the scala code for easier comparison.
-/
public def scanList (w : List T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.length)
    (pre : Nat) : BinItems T N :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Pointer.predecessor pre⟩]
  else
    []

/--
List-based implementation of the .predict operation.

Returns a fresh item for each rule, which got `A` as its lhs.
-/
public def predictList (G : ContextFreeGrammarList T N) (A : N) (k : Nat) : BinItems T N :=
  let rules := G.rules.filter (fun r => r.input == A)
  rules.map (fun r => ⟨⟨r,0,k,k⟩, Pointer.null⟩)

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def completeList (y : EarleyItem T N) {n : Nat} (bins : EarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : BinItems T N :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (BinItem T N × Nat) := filterWithIdx bins[y.startIdx]
    (fun x => nextSymbol x.item == some (Symbol.nonterminal y.rule.input))
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x.item y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
This version of completeList lends itself easier to reason with in a specific situation,
while performing worse without lazyness in linked lists or chaining maps.
The difference in performance is most apparent for grammar 2/3.
-/
public def completeListI (y : EarleyItem T N) {n : Nat} (bins : EarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : BinItems T N :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := filterWithIdx (items bins[y.startIdx])
    (fun x => nextSymbol x == some (Symbol.nonterminal y.rule.input))
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

omit [LawfulBEq (EarleyItem T N)] in
theorem completeList_eq_completeListI (y : EarleyItem T N) {n : Nat} (bins : EarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : completeList y bins h j = completeListI y bins h j := by
  simp only [completeList, filterWithIdx, completeListI, items]
  let P := fun x : BinItem T N => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)
  fun_induction filterWithIdxAux P 0 bins[y.startIdx] <;> grind

/--
Returns the list appended with an element, if it is not already part of the list,
while also merging any reduction pointers for duplicate items.
Predecessor pointers are unique, so duplicate items can be safely discarded
-/
@[inline, grind]
public def updateBinAux :  BinItem T N  → BinItems T N → BinItems T N
  | y, [] => [y]
  | y, x::xs => match (x,y) with
    | (⟨xItem, Pointer.reduction xp xP⟩,⟨yItem, Pointer.reduction yp yP⟩) =>
      -- Merge any reduction pointers if the items match
      if xItem == yItem then
        ⟨xItem, Pointer.reduction xp (yp::yP.append xP)⟩::xs
      else
        -- Search further, if no match
        x::(updateBinAux y xs)
    | _ =>
      -- Abort, if an item with an irrelevant pointer already exists in the List
      if x.item == y.item then
        x::xs
      else
        -- Search further, if no match
        x::(updateBinAux y xs)

/--
Add given list one by one into `xs`, if they are not already part of `xs`,
while also merging any reduction pointers.
-/
@[inline, grind]
public def updateBin (xs : BinItems T N) : BinItems T N → BinItems T N
  | [] => xs
  | y::ys => updateBin (updateBinAux y xs) ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBins {n : Nat} (bins : EarleyBins T N n) (k : Nat) (newBin : BinItems T N) :
    EarleyBins T N n :=
  Vector.modify bins k (fun x => updateBin x newBin)

omit [LawfulBEq (EarleyItem T N)] in
@[simp, grind =]
lemma updateBinAux_nil (y : BinItem T N) : updateBinAux y [] = [y] := by simp [updateBinAux]

omit [LawfulBEq (EarleyItem T N)] in
@[simp, grind =]
lemma updateBin_nil (xs : BinItems T N) : updateBin xs [] = xs := by simp [updateBin]

theorem memItem_of_updateBinAux (xs : BinItems T N) (y : BinItem T N) (x : EarleyItem T N)
    (hmem : x ∈ items (updateBinAux y xs)) : x ∈ items xs ∨ x = y.item := by
  induction xs with
  | nil => grind
  | cons head tail ih => grind

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma wfBinPointers_of_updatedBins (w : List T) {k : Nat}
    (bins bins' : EarleyBins T N (w.length + 1)) (hk : k < w.length + 1)
    (hbins' : ∀ i, (hi : i ≤ w.length) → bins[i].length ≤ bins'[i].length)
    (h : BinPointers.WF w bins bins'[k] k) :
    BinPointers.WF w bins' bins'[k] k := by
  simp only [BinPointers.WF]
  simp only [BinPointers.WF] at h
  intro x hmem
  specialize h x hmem
  simp only [Pointer.WF, tsub_le_iff_right]
  simp only [Pointer.WF, tsub_le_iff_right] at h
  split <;> grind

omit [LawfulBEq (EarleyItem T N)] in
/--
Using updateBinAux on a List with no duplicates, results in a list with no duplicates as well.
-/
lemma noDup_of_updateBinAux (xs : BinItems T N) (y : BinItem T N)
    [LawfulBEq (EarleyItem T N)] (hx : (items xs).Nodup) :
    items (updateBinAux y xs) |>.Nodup := by
  fun_induction updateBinAux y xs with
  | case1 => grind
  | case2 => grind
  | case3 y x xs =>
    have := memItem_of_updateBinAux xs y
    grind
  | case4 => grind
  | case5 y x xs =>
    have := memItem_of_updateBinAux xs y
    grind

omit [LawfulBEq (EarleyItem T N)] in
/--
Using updateBin on a List with no duplicates, results in a list with no duplicates as well.
-/
theorem noDup_of_updateBin (xs ys : BinItems T N) (hx : (items xs).Nodup)
    [LawfulBEq (EarleyItem T N)] : items (updateBin xs ys) |>.Nodup := by
  fun_induction updateBin xs ys with
  | case1 xs => grind
  | case2 xs y ys ih1 => grind [noDup_of_updateBinAux xs y]

lemma wfBinItems_of_updateBinAux (G : ContextFreeGrammarList T N) (w : List T) {k : Nat}
    (bin : BinItems T N) (hwfbin : BinItems.WF G w k bin) (y : BinItem T N)
    (hwfy : isWellFormed G.rules w.length y.item ∧ y.item.endIdx = k) :
    BinItems.WF G w k (updateBinAux y bin)  := by
  induction bin with
  | nil => grind
  | cons x xs ih => grind

@[simp, grind =]
theorem updateBinAux_cons (xs : BinItems T N) (y : BinItem T N) (hmem : y.item ∉ items xs) :
    updateBinAux y xs = xs ++ [y] := by
  induction xs generalizing y with
  | nil => grind
  | cons head tail ih => grind

omit [LawfulBEq (EarleyItem T N)] in
lemma length_le_lengthUpdateBinAux (xs : BinItems T N) (y : BinItem T N) :
    xs.length ≤ (updateBinAux y xs).length := by
  induction xs generalizing y with
  | nil => grind
  | cons x xs ih => grind

omit [LawfulBEq (EarleyItem T N)] in
lemma length_le_lengthUpdateBin (xs ys : BinItems T N) :
    xs.length ≤ (updateBin xs ys).length := by
  induction ys generalizing xs with
  | nil => grind
  | cons x xs ih => grind [length_le_lengthUpdateBinAux]

omit [LawfulBEq (EarleyItem T N)] in
lemma lengthNth_le_lengthUpdateBinNth {n : Nat} (bins : EarleyBins T N n) (ys : BinItems T N)
    (i k : Nat) (hi : i < n) : bins[i].length ≤ (updateBins bins k ys)[i].length := by
  induction ys generalizing bins with
  | nil => grind
  | cons x xs ih => grind [length_le_lengthUpdateBinAux, length_le_lengthUpdateBin]

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

theorem updateBinAux_of_updRed (xs xs' : BinItems T N) (y : BinItem T N) (i : Nat)
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
    · if h : x.item = y.item then
        clear ih
        simp only [updateBinAux, beq_iff_eq, List.append_eq]
        have hxP : x.pointer = Pointer.reduction xp xP := by grind
        have hx2 : x = ⟨x.item, Pointer.reduction xp xP⟩ := by rw [← hxP]
        have hy2 : y = ⟨x.item, Pointer.reduction yp yP⟩ := by rw [← hy]; rw [h]
        grind
      else
        have hi : i - 1 < xs.length := by grind
        specialize ih (updateBinAux y xs) y (i-1) (by grind [List.Nodup.of_cons]) hi
        have xs1 : xs[i - 1].pointer = Pointer.reduction xp xP := by grind
        have h2 : y.item = xs[i - 1].item := by grind
        specialize ih xs1 h2 hy (by simp)
        have ⟨h3, _⟩ := ih.right ih.left
        grind
    · intro j hk hneq
      have := updateBinAux_of_Red_of_neqItem (x::xs) y i j
      grind

lemma updateBinAux_of_Red_of_eqItem (xs : BinItems T N) (y : BinItem T N) (i j : Nat)
    (hNoDup : (items xs).Nodup) {yp : ReductionPointer} {yP : List ReductionPointer}
    (hy : y.pointer = .reduction yp yP) (hi : i < xs.length)
    (hx : xs[i].pointer = .null ∨ xs[i].pointer = .predecessor j) (heq : y.item = xs[i].item) :
    updateBinAux y xs = xs := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

omit [LawfulBEq (EarleyItem T N)] in
lemma wfBinPointers_of_updateBinAux (w : List T) {k : Nat} (bins : EarleyBins T N (w.length + 1))
    (xs : BinItems T N) (hwfbin : BinPointers.WF w bins xs k)
    (y : BinItem T N) (hwfy : Pointer.WF w bins y.pointer k) :
    BinPointers.WF w bins (updateBinAux y xs) k := by
  induction xs with
  | nil => grind
  | cons x xs ih =>
    simp only [updateBinAux, List.append_eq]
    split
    · split
      · rename_i xp xP _ _ _ _ _
        have hxP : x.pointer = Pointer.reduction xp xP := by grind
        grind
      · grind
    · split <;> grind

lemma wfBinItems_of_updateBin (G : ContextFreeGrammarList T N) (w : List T) {k : Nat}
    (xs ys : BinItems T N) (hwfx : BinItems.WF G w k xs)
    (hwfy : ∀ y ∈ ys, isWellFormed G.rules w.length y.item ∧ y.item.endIdx = k) :
    BinItems.WF G w k (updateBin xs ys)  := by
  induction ys generalizing xs with
  | nil => grind
  | cons y ys ih => grind [wfBinItems_of_updateBinAux, noDup_of_updateBin]

omit [LawfulBEq (EarleyItem T N)] in
lemma wfBinPointers_of_updateBin (w : List T) {k : Nat} (bins : EarleyBins T N (w.length + 1))
    (xs : BinItems T N) (hwfbin : BinPointers.WF w bins xs k)
    (ys : BinItems T N) (hwfy : ∀ y ∈ ys, Pointer.WF w bins y.pointer k) :
    BinPointers.WF w bins (updateBin xs ys) k := by
  induction ys generalizing xs with
  | nil => grind
  | cons y ys ih =>
    have hwfAux := wfBinPointers_of_updateBinAux w bins xs hwfbin y (by grind)
    grind

lemma soundPointers_of_updateBinAux (w : List T) {k : Nat} (bins : EarleyBins T N (w.length + 1))
    (hbins : ∀ k, (hk : k ≤ w.length) → (items bins[k]).Nodup ∧ ∀ j, (hj : j < bins[k].length)
      → Pointer.isSound bins[k][j].pointer k j)
    (y : BinItem T N) (hk : k < w.length + 1) (hwf : Pointer.isSound y.pointer k bins[k].length) :
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
        have := updateBinAux_of_Red_of_eqItem bins[k] y j' 0 this hy (by grind) (by simp [hb]) heq'
        grind
      | .predecessor i =>
        have := (hbins k (by grind)).left
        have heq' : y.item = bins[k][j'].item := by
          simp only [items, List.getElem_map] at heq
          simp [heq]
        have := updateBinAux_of_Red_of_eqItem bins[k] y j' i this hy (by grind) (by simp [hb]) heq'
        grind
      | .reduction bp bP =>
        have hnDup := (hbins k (by grind)).left
        have : y.item = bins[k][j'].item := by grind
        have hupdRed := updateBinAux_of_updRed bins[k] (updateBinAux y bins[k]) y j' hnDup hj'
            hb this hy (by simp)
        grind

-- I cannot really simplify the goal and make the proof easier for me
-- since any item of ys can get merged into the bins and thus the `< j` would get problematic.
lemma soundPointers_of_updateBin (w : List T) (k : Nat) (bins : EarleyBins T N (w.length + 1))
    (hbins : ∀ k, (hk : k ≤ w.length) → (items bins[k]).Nodup ∧ ∀ j, (hj : j < bins[k].length)
      → Pointer.isSound bins[k][j].pointer k j)
    (ys : BinItems T N) (hk : k < w.length + 1)
    (hwf : ∀ y ∈ ys, Pointer.isSound y.pointer k bins[k].length) :
    ∀ j, (hj : j < (updateBin bins[k] ys).length) →
    Pointer.isSound (updateBin bins[k] ys)[j].pointer k j := by
  induction ys generalizing bins with
  | nil => grind
  | cons y ys ih =>
    intro j hj
    let bins' := Vector.set bins k (updateBinAux y bins[k]) hk
    have hSaux := soundPointers_of_updateBinAux w bins hbins y hk (by grind)
    have : ∀ y ∈ ys, Pointer.isSound y.pointer k bins'[k].length := by
      clear ih
      simp only [Pointer.isSound]
      grind [length_le_lengthUpdateBinAux]
    have hbins' : (∀ (k : ℕ) (hk : k ≤ w.length), (items bins'[k]).Nodup ∧
        ∀ (j : ℕ) (hj : j < bins'[k].length), Pointer.isSound bins'[k][j].pointer k j) := by
      clear this
      intro k2 hk2
      constructor
      · grind [noDup_of_updateBinAux bins[k] y]
      · grind
    specialize ih bins' hbins' (by grind)
    grind

lemma wfBins_of_updateBin (G : ContextFreeGrammarList T N) (w : List T) {k : Nat}
    (bins : EarleyBins T N (w.length + 1)) (hwf : EarleyBins.WF G w bins)
    (ys : BinItems T N) (hk : k < w.length + 1)
    (hwfy : ∀ y ∈ ys, isWellFormed G.rules w.length y.item ∧ y.item.endIdx = k)
    (hwfPy : BinPointers.WF w bins ys k)
    (hwfSy : ∀ y ∈ ys, Pointer.isSound y.pointer k bins[k].length) :
    EarleyBins.WF G w (updateBins bins k ys)  := by
  intro i hi
  if heq : i = k then
    refine ⟨by grind [noDup_of_updateBin], by grind [wfBinItems_of_updateBin], ?_, ?_⟩
    · have ⟨h0,h1,h2,h3⟩ := hwf k (by lia)
      simp only [heq]
      have hwfb : BinPointers.WF w bins (updateBins bins k ys)[k] k := by
        have := wfBinPointers_of_updateBin w bins bins[k] h2 ys (by grind)
        grind
      have : ∀ (i : ℕ) (hi : i ≤ w.length), bins[i].length
          ≤ (updateBins bins k ys)[i].length := by grind [lengthNth_le_lengthUpdateBinNth]
      have := wfBinPointers_of_updatedBins w bins (updateBins bins k ys) hk this hwfb
      grind
    · intro j hj
      have := soundPointers_of_updateBin w k bins (by grind) ys
      grind
  else
    refine ⟨by grind, ?_⟩
    have ⟨h1,h2⟩ := hwf k (by lia)
    have hi : i < w.length + 1 := by lia
    have : ∀ (i : ℕ) (hi : i ≤ w.length), bins[i].length ≤ (updateBins bins k ys)[i].length := by
      grind [lengthNth_le_lengthUpdateBinNth]
    have := wfBinPointers_of_updatedBins w bins (updateBins bins k ys) hi this
    grind

omit [BEq T] in
lemma wfBinItems_of_initList (G : ContextFreeGrammarList T N) (w : List T) :
    (items (initList G)).Nodup ∧ BinItems.WF G w 0 (initList G)  := by
  have := G.nodup
  grind [initList]

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_scanList {G : ContextFreeGrammarList T N} {w : List T} (j k : Nat) {a : T}
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (x : EarleyItem T N) (hk : k < w.length) (hmemx : x ∈ (items bins[k]))
    (hnext : nextSymbol x = some (Symbol.terminal a))
    (y : BinItem T N) (hmemy : y ∈ scanList w x a k hk j) :
    isWellFormed G.rules w.length y.item ∧ y.item.endIdx = k + 1 := by
  grind [scanList]

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_scanList {w : List T} (j k : Nat) {a : T} {bins : EarleyBins T N (w.length + 1)}
    (x : EarleyItem T N) (hk : k < w.length) (hj : ¬ (j ≥ bins[k].length)) :
    BinPointers.WF w bins (scanList w x a k hk j) (k+1) := by
  grind [scanList]

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_scanList {w : List T} (j k : Nat) {a : T}
    {bins : EarleyBins T N (w.length + 1)} (x : EarleyItem T N) (hk : k < w.length) :
    ∀ y ∈ scanList w x a k hk j, Pointer.isSound y.pointer (k+1) bins[k+1].length := by
  grind [scanList]

lemma wfBins_of_scanList {G : ContextFreeGrammarList T N} {w : List T} {j k : Nat} {a : T}
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (x : EarleyItem T N) (hk : k < w.length) (hj : ¬ (j ≥ bins[k].length))
    (hx : x = (bins[k][j]).item) (hnext : nextSymbol x = some (Symbol.terminal a)) :
    EarleyBins.WF G w (updateBins bins (k+1) (scanList w x a k hk j)) := by
  apply wfBins_of_updateBin G w bins hbins (scanList w x a k hk j) (by lia)
  · exact wfItems_of_scanList j k hbins x hk (by grind) hnext
  · grind [wfPointers_of_scanList]
  · grind [soundPointers_of_scanList]

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_predictList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat) (A : N)
    (hk : k ≤ w.length) (y : EarleyItem T N) (hmemy : y ∈ (items (predictList G A k))) :
    isWellFormed G.rules w.length y ∧ y.endIdx = k := by
  grind [predictList]

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_predictList (G : ContextFreeGrammarList T N) {w : List T} (k : Nat) (A : N)
    {bins : EarleyBins T N (w.length + 1)} :
    BinPointers.WF w bins (predictList G A k) k := by
  grind [predictList]

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_predictList (G : ContextFreeGrammarList T N) {w : List T} (k : Nat) (A : N)
    (bins : EarleyBins T N (w.length + 1)) (hk : k < w.length + 1) :
    ∀ x ∈ predictList G A k, Pointer.isSound x.pointer k bins[k].length := by
  grind [predictList]

-- hj is a negation for direct reasoning with earleyBinList
lemma wfBins_of_predictList {G : ContextFreeGrammarList T N} {w : List T} {A : N} {k : Nat}
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (hk : k < w.length + 1) :
    EarleyBins.WF G w (updateBins bins k (predictList G A k)) := by
  apply wfBins_of_updateBin G w bins hbins (predictList G A k) hk
  · grind [wfItems_of_predictList]
  · grind [wfPointers_of_predictList]
  · grind [soundPointers_of_predictList]

omit [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_completeList {G : ContextFreeGrammarList T N} {w : List T} (j k : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hmemy : y ∈ (items bins[k]))
    (x : EarleyItem T N) (hmemx : x ∈ (items (completeList y bins (by grind) j))) :
    isWellFormed G.rules w.length x ∧ x.endIdx = k := by
  simp only [completeList, items, List.map_map, List.mem_map, Function.comp_apply,
    Prod.exists] at hmemx
  let P := fun x : BinItem T N => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)
  let originBin := bins[y.startIdx]'(by grind)
  let filteredOriginBin := filterWithIdx originBin P
  have := filterWithIdx_cong_filter originBin P
  -- z is the original item, which will be completed
  rcases hmemx with ⟨z,_,hInc⟩
  have : z ∈ filteredOriginBin.map Prod.fst := by grind
  grind

omit [LawfulBEq (EarleyItem T N)] in
lemma wfPointers_of_completeList {G : ContextFreeGrammarList T N} {w : List T} (j k : Nat)
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hmemy : y ∈ (items bins[k]))
    (hj : j < bins[k].length) :
    BinPointers.WF w bins (completeList y bins (by grind) j) k := by
  simp only [BinPointers.WF]
  intro x hmemx
  simp only [completeList, List.mem_map, Prod.exists] at hmemx
  let P := fun x : BinItem T N => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)
  let originBin := bins[y.startIdx]'(by grind)
  let filteredOriginBin := filterWithIdx originBin P
  simp only [Pointer.WF, tsub_le_iff_right]
  -- z is the original item, which will be completed
  rcases hmemx with ⟨z,zIdx,⟨hmemz,hx⟩⟩
  have xP : x.pointer = Pointer.reduction ⟨y.startIdx, zIdx, j⟩ [] := by grind
  simp only [xP]
  refine ⟨by lia, by grind, ?_, by grind⟩
  intro hbounds
  exact filterWithIdx_le_length bins[y.startIdx]
    (fun x => x.item.nextSymbol == some (Symbol.nonterminal y.rule.input)) zIdx (by grind)

omit [LawfulBEq (EarleyItem T N)] in
lemma soundPointers_of_completeList (G : ContextFreeGrammarList T N) {w : List T} (j k : Nat)
    (bins : EarleyBins T N (w.length + 1)) (hbins : EarleyBins.WF G w bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hmemy : y ∈ (items bins[k]))
    (hj : j < bins[k].length) :
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
  specialize hbins k (by grind)
  have inv := hbins.right.right
  simp only [Pointer.isSound] at inv
  have : y.startIdx < k ∨ y.startIdx = k := by grind
  rcases this with h | h
  · grind
  · simp only [h, lt_self_iff_false, true_and, false_or, gt_iff_lt]
    exact filterWithIdx_le_length bins[k] P zIdx (by grind)

-- hj is a negation for direct reasoning with earleyBinList
lemma wfBins_of_completeList {G : ContextFreeGrammarList T N} {w : List T} {j k : Nat}
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hj : ¬ (j ≥ bins[k].length))
    (hy : y = bins[k][j].item) : EarleyBins.WF G w
    (updateBins bins k (completeList y bins (by grind) j)) := by
  apply wfBins_of_updateBin G w bins hbins (completeList y bins (by grind) j) hk
  · grind [wfItems_of_completeList j k hbins y]
  · grind [wfPointers_of_completeList j k hbins y hk (by grind) (by lia)]
  · grind [soundPointers_of_completeList G j k bins hbins y hk]

lemma wfBins_of_earleyBinList {G : ContextFreeGrammarList T N} {w : List T} (j k : Nat)
    (bins bins' : EarleyBins T N (w.length + 1)) (hbins : EarleyBins.WF G w bins)
    (hk : k < bins.size) (hj : ¬ (j ≥ bins[k].length))
    (h : bins' =
      let x := bins[k][j]
      match nextSymbol x.item with
      | some s => match s with
        | Symbol.nonterminal A =>
          let newItems := predictList G A k
          updateBins bins k newItems
        | Symbol.terminal a =>
          if hk : k ≥ w.length then
            bins
          else
            let newItem := scanList w x.item a k (by lia) j
            updateBins bins (k + 1) newItem
      | none =>
        let newItems := completeList x.item bins (by grind) j
        updateBins bins k newItems) :
    EarleyBins.WF G w bins' := by
  simp only [h, ge_iff_le]
  match hnext : nextSymbol bins[k][j].item with
  | some s => match s with
    | Symbol.nonterminal A => grind [wfBins_of_predictList]
    | Symbol.terminal a =>
      if hk : k ≥ w.length then
        simp [hk, hbins]
      else
        grind [wfBins_of_scanList]
  | none => grind [wfBins_of_completeList]

lemma length_lte_ncard_of_superset {α : Type} (xs : List α) (s : Set α) [Finite s]
    (P : α → Prop) (hs : s = { x | P x }) (hx : ∀ x ∈ xs, P x) (hNoDup : xs.Nodup) :
    xs.length ≤ s.ncard := by
  have : xs.length ≤ { x | x ∈ xs }.ncard := by
    induction xs with
    | nil => grind
    | cons y ys ih =>
      specialize ih (by grind) (by grind)
      simp only [List.length, List.mem_cons]
      have : { x | x ∈ ys }.ncard + 1 = { x | x = y ∨ x ∈ ys }.ncard := by
        have : { x | x ∈ ys } = { x | x = y ∨ x ∈ ys } \ {y} := by
          ext
          grind
        have : Finite { x | x = y ∨ x ∈ ys } := by grind [Finite.Set.subset]
        have : y ∈ { x | x = y ∨ x ∈ ys } := by grind
        have := Set.ncard_sdiff_singleton_add_one this
        grind
      grind
  have hcard : { x | x ∈ xs }.ncard ≤ s.ncard := Set.ncard_le_ncard (by grind)
  grind

end WellFormedBin

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma decreasingAux {G : ContextFreeGrammarList T N} {w : List T}
    {bins : EarleyBins T N (w.length + 1)} (hbins : EarleyBins.WF G w bins)
    (j k : Nat) (hk : k < w.length + 1) (hj : j < bins[k].length) :
    {x | isWellFormed G.rules w.length x}.ncard + 1 - (j + 1) <
    {x | isWellFormed G.rules w.length x}.ncard + 1 - j := by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules w.length x }
    have : (items bins[k]).length ≤ wfItemsBin.ncard := by
      have hF := Earley.Proofs.Finiteness.finiteEarleyWF G w.length
      have ⟨hNoDup, _⟩ := hbins
      let P := (fun x => isWellFormed G.rules w.length x)
      apply length_lte_ncard_of_superset (items bins[k]) wfItemsBin P (by grind) (by grind) hNoDup
    grind
  · simp

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList {G : ContextFreeGrammarList T N} {w : List T}
    (bins : EarleyBins T N (w.length + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : EarleyBins.WF G w bins) : WfEarleyBins G w :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].length then
    ⟨bins, hbins⟩
  else
    let x := bins[k][j]
    let bins' := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A k
        updateBins bins k newItems
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.length then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanList w x.item a k (by lia) j
          updateBins bins (k+1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeList x.item bins (by grind) j
      updateBins bins k newItems
    have : EarleyBins.WF G w bins' := by grind [wfBins_of_earleyBinList]
    earleyBinList bins' k hk (j+1) this
termination_by { x | isWellFormed G.rules w.length x }.ncard + 1 - j
decreasing_by exact decreasingAux hbins j k (by lia) (by lia)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initBins (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBins G w :=
  let b₀ := initList G
  let bins := Vector.replicate (w.length + 1) []
  let bins' := bins.set 0 b₀ (by simp)
  have : EarleyBins.WF G w bins' := by
    have := wfBinItems_of_initList G w
    grind [initList]
  ⟨bins', this⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (h : k < w.length + 1) : WfEarleyBins G w :=
  match h : k with
  | 0 =>
    let wfBins := initBins G w
    earleyBinList wfBins.bins 0 (by lia) 0 wfBins.inv
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let ⟨mBins, inv⟩ := earleyBinsList G w i (by lia)
    earleyBinList mBins k (by lia) 0 inv

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyList (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBins G w :=
  earleyBinsList G w w.length (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w |>.bins
  let finalItems := items bins[w.length]
  ∃ x ∈ finalItems, isFinished G.initial w.length x

end Recognizer
end Earley
