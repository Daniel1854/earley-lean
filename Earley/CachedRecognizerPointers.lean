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
public import Earley.Recognizer
public import Mathlib.Data.Set.Card

/-!

This module represents an optimized implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to the naive implementation in `Recognizer`:
- it caches if an item already exists in a bin: HashMap (EarleyItem T N) Nat
- it caches the indices for the items that can be completed: HashMap N (List (EarleyItem T N × Nat))

These optimizations do make it such that maintaining only one origin information per binitem
would be way more convenient, and since the implementation for `build_tree` only uses
the first pointer of the reduction pointer anyway, this doesn't affect the algorithms currently.
This could be a more appropriate next step instead of the current implementation?

TODO: CachedParser would use `Array.findIdx?` instead of filterWithIdx?
-/

@[expose] public section

namespace Earley
namespace CachedRecognizerPointers

open Model
open EarleyItem
open Utils

/--
A cache for checking if an items resides within a single bin.
Maps an EarleyItem to its index within the bin.
-/
abbrev ItemCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] : Type :=
  Std.HashMap (EarleyItem T N) Nat

/--
A cache for accessing the possible rules for a completion within a single bin.
Maps a non-terminal to all the EarleyItems that the bin contains for it and
their index within the bin.
-/
abbrev CompletionCache (T N : Type) [BEq N] [Hashable N] : Type :=
  Std.HashMap N (List (EarleyItem T N × Nat))

abbrev BinItems (T N : Type) : Type :=
  Array (Recognizer.BinItem T N)

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : BinItems T N
  items : ItemCache T N
  completions : CompletionCache T N

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)]

@[grind]
def items (bin : BinItems T N) : Array (EarleyItem T N) :=
  bin.map (fun x => x.item)

section WellFormedBin

/--
A pointer is well-formed with respect to a CachedEarleyBin, if TODO
TODO: Since the pointers require access to previous bins, it's a bit inconvenient to merge.
      I could make CachedBinPointers.WF reason about the index and simply merge?
      But the proofs get quite a bit more involved then.
-/
@[grind]
public def Pointer.WF (w : Array T) (bins : CachedEarleyBins T N (w.size + 1))
    (pointer : Recognizer.Pointer) (k : Nat) : Prop :=
  match pointer with
  | .null => True
  | .predecessor i => k ≠ 0 ∧ k - 1 ≤ w.size ∧ ((h : k - 1 ≤ w.size) → i < bins[k-1].raw.size)
  | .reduction p ps => k ≤ w.size ∧ p.endIdxA ≤ w.size ∧
      ((h : p.endIdxA ≤ w.size) → p.i < bins[p.endIdxA].raw.size) ∧
      ((h : k ≤ w.size) → p.j < bins[k].raw.size)

@[grind]
public def BinPointers.WF (w : Array T) (bins : CachedEarleyBins T N (w.size + 1))
    (bin : BinItems T N) (k : Nat) : Prop :=
  ∀ x ∈ bin, Pointer.WF w bins x.pointer k

/--
CachedEarleyBins are well-formed, if all of its bins and its caches are well-formed.
-/
@[grind]
public def CachedEarleyBins.WF (G : ContextFreeGrammarList T N) (w : Array T)
    (bins : CachedEarleyBins T N (w.size + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → (items bins[k].raw).toList.Nodup
    ∧ Recognizer.BinItems.WF G w.toList k bins[k].raw
    ∧ BinPointers.WF w bins bins[k].raw k
    ∧ ∀ j, (hj : j < bins[k].raw.size) → Recognizer.Pointer.isSound bins[k].raw[j].pointer k j
  -- FIXME: missing invariant about the cache stating that the items correspond
  --        to the items in each bin ? Or do I want to prove this separately?
  --∧ something about itemCache corresponding to the items in each bin
  --∧ something about completionCache corresponding to the filtered items in each bin

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (w : Array T) where
  bins : CachedEarleyBins T N (w.size + 1)
  inv : CachedEarleyBins.WF G w bins

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
-/
public def scanCached (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
    (pre : Nat) : List (Recognizer.BinItem T N) :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Recognizer.Pointer.predecessor pre⟩]
  else
    []

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : List (Recognizer.BinItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Recognizer.Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBinCached (bin : CachedEarleyBin T N) :
    List (Recognizer.BinItem T N) → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      have : idx < bin.raw.size := by sorry -- some wf cache argument
      match (bin.raw[idx], y) with
      | (⟨xItem, Recognizer.Pointer.reduction xp xP⟩,
          ⟨yItem, Recognizer.Pointer.reduction yp yP⟩) =>
        let updItem := ⟨xItem, Recognizer.Pointer.reduction xp (yp::yP.append xP)⟩
        updateBinCached { bin with raw := (bin.raw.swapAt idx updItem this).snd } ys
      | _ => updateBinCached bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y.item bin.raw.size
      match y.item.nextSymbol with
      | some (Symbol.nonterminal n) =>
        let completions' := bin.completions.alter n (fun zs => match zs with
          | some zs => zs.append [⟨y.item, bin.raw.size⟩]
          | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))
        updateBinCached ⟨raw', items', completions'⟩ ys
      | _ =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        updateBinCached ⟨raw', items', bin.completions⟩ ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : List (Recognizer.BinItem T N)) : CachedEarleyBins T N n :=
  Vector.modify bins k (fun x => updateBinCached x newBin)

end WellFormedBin

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : CachedEarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : CachedEarleyBins.WF G w bins) : WfEarleyBinsCached G w :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].raw.size then
    ⟨bins, hbins⟩
  else
    let x := bins[k].raw[j]
    let bins' := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := Recognizer.predictList G A k
        updateBinsCached bins k newItems
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.size then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanCached w x.item a k (by omega) j
          updateBinsCached bins (k+1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCached x.item bins (by grind) j
      updateBinsCached bins k newItems
    have : CachedEarleyBins.WF G w bins' := by sorry
    earleyBinList bins' k (by omega) (j+1) this
termination_by { x | isWellFormed G.rules (mapT w.toList) x }.ncard + 1 - j
decreasing_by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules (mapT w.toList) x }
    have : (items bins[k].raw).toList.length ≤ wfItemsBin.ncard := by
      have hF := Earley.Proofs.Finiteness.finiteEarleyWF G (mapT w.toList)
      have ⟨hNoDup, _, _, _⟩ := hbins
      let P := (fun x => isWellFormed G.rules (mapT w.toList) x)
      apply Recognizer.length_lte_ncard_of_superset (items bins[k].raw).toList wfItemsBin P
        (by grind) (by grind) hNoDup
    grind
  · simp

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
TODO: I could use of Std.HashSet.ofList and something more clever for the HashMap cache,
      but utilizing updateBin is easier to reason with. It shouldnt be much worse perf-wise
      Reasoning becomes more difficult as well though.
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) : WfEarleyBinsCached G w :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  let bins := Vector.replicate (w.size + 1) ⟨Array.empty,  {},  {}⟩
  let bins' := updateBinsCached bins 0 (Recognizer.initList G)
  have : CachedEarleyBins.WF G w bins' := by
    have := G.nodup
    simp only [CachedEarleyBins.WF, Order.lt_add_one_iff]
    intro k hk
    if hk : k = 0 then
      sorry
    else
      --grind [Recognizer.initList]
      sorry
  ⟨bins', this⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (h : k < w.size + 1) : WfEarleyBinsCached G w :=
  match h : k with
  | 0 =>
    let ⟨bins, inv⟩ := initCachedBins G w
    earleyBinList bins 0 (by simp) 0 inv
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let ⟨bins, inv⟩ := earleyBinsList G w i (by lia)
    earleyBinList bins k (by lia) 0 inv

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyList (G : ContextFreeGrammarList T N) (w : Array T) : WfEarleyBinsCached G w :=
  earleyBinsList G w w.size (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeList (G : ContextFreeGrammarList T N) (w : Array T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w |>.bins
  let finalItems := items bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial (mapT w.toList) x

end CachedRecognizerPointers
end Earley
