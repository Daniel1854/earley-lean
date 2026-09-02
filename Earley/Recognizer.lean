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
- all items in the bin are well-formed with respect to a bound
- the endIdx of all items match the index of the bin
-/
@[grind]
public def BinItems.WF (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (bin : BinItems T N) : Prop :=
  (items bin).Nodup ∧ ∀ x ∈ bin, isWellFormed G.rules w.size x.item ∧ x.item.endIdx = k

/--
EarleyBins are well-formed, if all of its bins are well-formed.
-/
@[grind]
public def EarleyBins.WF (G : ContextFreeGrammarList T N) {w : Array T}
    (bins : EarleyBins T N (w.size + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → BinItems.WF G w k bins[k]

/--
A combination of an EarleyBins with a well-formedness Invariant about it.
-/
public structure WfEarleyBins (G : ContextFreeGrammarList T N) (w : Array T) where
  bins : EarleyBins T N (w.size + 1)
  inv : EarleyBins.WF G bins

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
-/
public def scanList (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
    (pre : Nat) : BinItems T N :=
  if w[k] == a then
    [⟨incItem x (k+1), Pointer.predecessor pre⟩]
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
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x.item y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

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
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

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
public def updateBinAux : BinItem T N  → BinItems T N → BinItems T N
  | y, [] => [y]
  | y, x::xs =>
    if x.item == y.item then
      match (x.pointer, y.pointer) with
      -- Merge any reduction pointers for matching items
      | (Pointer.reduction xp xP, Pointer.reduction yp yP) =>
        ⟨y.item, Pointer.reduction xp (yp::yP.append xP)⟩::xs
      -- Abort, if an item with an irrelevant pointer already exists in the List
      | _ => x::xs
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

omit [LawfulBEq (EarleyItem T N)] in
theorem memItem_of_updateBinAux (xs : BinItems T N) (y : BinItem T N) (x : EarleyItem T N)
    (hmem : x ∈ items (updateBinAux y xs)) : x ∈ items xs ∨ x = y.item := by
  induction xs with
  | nil => grind
  | cons head tail ih => grind

lemma noDup_of_updateBinAux (xs : BinItems T N) (y : BinItem T N) (hx : (items xs).Nodup) :
    items (updateBinAux y xs) |>.Nodup := by
  fun_induction updateBinAux y xs with
  | case1 => grind
  | case2 => grind
  | case3 => grind
  | case4 y x xs =>
    have := memItem_of_updateBinAux xs y
    grind

theorem noDup_of_updateBin (xs ys : BinItems T N) (hx : (items xs).Nodup) :
    items (updateBin xs ys) |>.Nodup := by
  fun_induction updateBin xs ys with
  | case1 xs => grind
  | case2 xs y ys ih1 => grind [noDup_of_updateBinAux xs y]

lemma wfBinItems_of_updateBinAux (G : ContextFreeGrammarList T N) (w : Array T) {k : Nat}
    (bin : BinItems T N) (hwfbin : BinItems.WF G w k bin) (y : BinItem T N)
    (hwfy : isWellFormed G.rules w.size y.item ∧ y.item.endIdx = k) :
    BinItems.WF G w k (updateBinAux y bin)  := by
  induction bin with
  | nil => grind
  | cons x xs ih => grind [noDup_of_updateBinAux]

@[simp, grind =]
theorem updateBinAux_cons (xs : BinItems T N) (y : BinItem T N) (hmem : y.item ∉ items xs) :
    updateBinAux y xs = xs ++ [y] := by
  induction xs generalizing y with
  | nil => grind
  | cons head tail ih => grind

lemma wfBinItems_of_updateBin (G : ContextFreeGrammarList T N) (w : Array T) {k : Nat}
    (xs ys : BinItems T N) (hwfx : BinItems.WF G w k xs)
    (hwfy : ∀ y ∈ ys, isWellFormed G.rules w.size y.item ∧ y.item.endIdx = k) :
    BinItems.WF G w k (updateBin xs ys)  := by
  induction ys generalizing xs with
  | nil => grind
  | cons y ys ih => grind [wfBinItems_of_updateBinAux]

theorem wfBins_of_updateBin (G : ContextFreeGrammarList T N) (w : Array T) {k : Nat}
    (bins : EarleyBins T N (w.size + 1)) (hwf : EarleyBins.WF G bins)
    (ys : BinItems T N) (hwfy : ∀ y ∈ ys, isWellFormed G.rules w.size y.item ∧ y.item.endIdx = k) :
    EarleyBins.WF G (updateBins bins k ys) := by
  grind [wfBinItems_of_updateBin]

omit [BEq T] in
lemma wfBinItems_of_initList (G : ContextFreeGrammarList T N) (w : Array T) :
    (items (initList G)).Nodup ∧ BinItems.WF G w 0 (initList G)  := by
  have := G.nodup
  grind [initList]

omit [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_scanList {G : ContextFreeGrammarList T N} {w : Array T} (j k : Nat) {a : T}
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (x : EarleyItem T N) (hk : k < w.size) (hmemx : x ∈ (items bins[k]))
    (hnext : nextSymbol x = some (Symbol.terminal a))
    (y : BinItem T N) (hmemy : y ∈ scanList w x a k hk j) :
    isWellFormed G.rules w.size y.item ∧ y.item.endIdx = k + 1 := by
  grind [scanList]

lemma wfBins_of_scanList {G : ContextFreeGrammarList T N} {w : Array T} {j k : Nat} {a : T}
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (x : EarleyItem T N) (hk : k < w.size) (hj : ¬ (j ≥ bins[k].length))
    (hx : x = (bins[k][j]).item) (hnext : nextSymbol x = some (Symbol.terminal a)) :
    EarleyBins.WF G (updateBins bins (k+1) (scanList w x a k hk j)) := by
  apply wfBins_of_updateBin G w bins hbins (scanList w x a k hk j)
  exact wfItems_of_scanList j k hbins x hk (by grind) hnext

omit [BEq T] [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_predictList (G : ContextFreeGrammarList T N) (wlen k : Nat) (A : N)
    (hk : k ≤ wlen) (y : EarleyItem T N) (hmemy : y ∈ (items (predictList G A k))) :
    isWellFormed G.rules wlen y ∧ y.endIdx = k := by
  grind [predictList]

-- hj is a negation for direct reasoning with earleyBinList
lemma wfBins_of_predictList {G : ContextFreeGrammarList T N} {w : Array T} {k : Nat} {A : N}
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins) (hk : k < w.size + 1) :
    EarleyBins.WF G (updateBins bins k (predictList G A k)) := by
  apply wfBins_of_updateBin G w bins hbins (predictList G A k)
  grind [wfItems_of_predictList]

omit [LawfulBEq (EarleyItem T N)] in
lemma wfItems_of_completeList {G : ContextFreeGrammarList T N} {w : Array T} (j k : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hmemy : y ∈ (items bins[k]))
    (x : EarleyItem T N) (hmemx : x ∈ (items (completeList y bins (by grind) j))) :
    isWellFormed G.rules w.size x ∧ x.endIdx = k := by
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

-- hj is a negation for direct reasoning with earleyBinList
lemma wfBins_of_completeList {G : ContextFreeGrammarList T N} {w : Array T} {j k : Nat}
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (y : EarleyItem T N) (hk : k < bins.size) (hj : ¬ (j ≥ bins[k].length))
    (hy : y = bins[k][j].item) : EarleyBins.WF G
    (updateBins bins k (completeList y bins (by grind) j)) := by
  apply wfBins_of_updateBin G w bins hbins (completeList y bins (by grind) j)
  grind [wfItems_of_completeList j k hbins y]

theorem wfBins_of_earleyBinList {G : ContextFreeGrammarList T N} {w : Array T} (j k : Nat)
    (bins bins' : EarleyBins T N (w.size + 1)) (hbins : EarleyBins.WF G bins)
    (hk : k < bins.size) (hj : ¬ (j ≥ bins[k].length))
    (h : bins' =
      let x := bins[k][j]
      match nextSymbol x.item with
      | some s => match s with
        | Symbol.nonterminal A =>
          let newItems := predictList G A k
          updateBins bins k newItems
        | Symbol.terminal a =>
          if hk : k ≥ w.size then
            bins
          else
            let newItem := scanList w x.item a k (by lia) j
            updateBins bins (k + 1) newItem
      | none =>
        let newItems := completeList x.item bins (by grind) j
        updateBins bins k newItems) : EarleyBins.WF G bins' := by
  simp only [h, ge_iff_le]
  match hnext : nextSymbol bins[k][j].item with
  | some s => match s with
    | Symbol.nonterminal A => grind [wfBins_of_predictList]
    | Symbol.terminal a =>
      if hk : k ≥ w.size then
        simp [hk, hbins]
      else
        grind [wfBins_of_scanList]
  | none => grind [wfBins_of_completeList]

theorem length_lte_ncard_of_superset {α : Type} (xs : List α) (s : Set α) [Finite s]
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
lemma decreasingAux {G : ContextFreeGrammarList T N} {w : Array T}
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins) (j k : Nat)
    (hk : k < w.size + 1) (hj : j < bins[k].length) :
    {x | isWellFormed G.rules w.size x}.ncard - (j + 1) <
    {x | isWellFormed G.rules w.size x}.ncard - j := by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules w.size x }
    have : (items bins[k]).length ≤ wfItemsBin.ncard := by
      have hF := Proofs.Finiteness.finiteWFEarleyItems G w.size
      have ⟨hNoDup, _⟩ := hbins
      let P := (fun x => isWellFormed G.rules w.size x)
      apply length_lte_ncard_of_superset (items bins[k]) wfItemsBin P (by grind) (by grind) hNoDup
    grind
  · simp

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : EarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : EarleyBins.WF G bins) : WfEarleyBins G w :=
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
        if hk : k ≥ w.size then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanList w x.item a k (by lia) j
          updateBins bins (k+1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeList x.item bins (by grind) j
      updateBins bins k newItems
    have : EarleyBins.WF G bins' := by grind [wfBins_of_earleyBinList]
    earleyBinList bins' k hk (j+1) this
termination_by { x | isWellFormed G.rules w.size x }.ncard - j
decreasing_by exact decreasingAux hbins j k (by lia) (by lia)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initBins (G : ContextFreeGrammarList T N) (w : Array T) : WfEarleyBins G w :=
  let b₀ := initList G
  let bins := Vector.replicate (w.size + 1) []
  let bins' := bins.set 0 b₀ (by simp)
  have : EarleyBins.WF G bins' := by
    have := wfBinItems_of_initList G w
    grind
  ⟨bins', this⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (h : k < w.size + 1) : WfEarleyBins G w :=
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
public def earleyList (G : ContextFreeGrammarList T N) (w : Array T) : WfEarleyBins G w :=
  earleyBinsList G w w.size (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.
-/
@[grind]
public def recognizeList (G : ContextFreeGrammarList T N) (w : Array T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w |>.bins
  let finalItems := items bins[w.size]
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end Recognizer
end Earley
