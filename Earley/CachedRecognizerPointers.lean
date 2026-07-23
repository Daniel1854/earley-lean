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
open Recognizer

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

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (BinItem T N)
  items : ItemCache T N
  completions : CompletionCache T N

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)]

@[grind]
def itemsA (bin : Array (BinItem T N)) : Array (EarleyItem T N) :=
  bin.map (fun x => x.item)

@[grind]
def rawList {wlen : Nat} (bins : CachedEarleyBins T N (wlen + 1)) : EarleyBins T N (wlen + 1) :=
  bins.map (fun x => x.raw.toList)

section WellFormedBin


/--
An ItemCache is well-formed, if it contains all elements of the raw array and the saved index
corresponds to the index within the raw array.
-/
@[grind]
public def ItemCache.WF (raw : Array (BinItem T N)) (items : ItemCache T N) : Prop :=
  ∀ i, (hi : i < raw.size) → items.contains raw[i].item
    ∧ ∃ (h : items.contains raw[i].item), items[raw[i].item] = i

/--
A CompletionCache is well-formed, if all elements of the raw array with their index are
members of the stored completionList for their input symbol of their rule.

With the way insertion goes, an inductive definition of WF would also have its merits, hm.
-/
@[grind]
public def CompletionCache.WF (raw : Array (BinItem T N)) (completions : CompletionCache T N) :
    Prop :=
  ∀ i, (hi : i < raw.size) → completions.contains raw[i].item.rule.input
    ∧ ∃ (h : completions.contains raw[i].item.rule.input),
      (raw[i].item, i) ∈ completions[raw[i].item.rule.input]

/--
The caches are well-formed, if both of them are well-formed.
-/
@[grind]
public def Cache.WF {wlen : Nat} (bins : CachedEarleyBins T N (wlen + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → ItemCache.WF bins[k].raw bins[k].items
    ∧ CompletionCache.WF bins[k].raw bins[k].completions

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (wlen : Nat) where
  bins : CachedEarleyBins T N (wlen + 1)
  inv : EarleyBins.WF G (rawList bins)
  -- TODO: Extend when I got the rest under control?
  --invCache : Cache.WF bins

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
-/
public def scanCached (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
    (pre : Nat) : List (BinItem T N) :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Pointer.predecessor pre⟩]
  else
    []

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : List (BinItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBinCached (bin : CachedEarleyBin T N) : List (BinItem T N) → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      have : idx < bin.raw.size := by sorry -- some wf cache argument
      match (bin.raw[idx], y) with
      | (⟨xItem, Pointer.reduction xp xP⟩, ⟨yItem, Pointer.reduction yp yP⟩) =>
        let updItem := ⟨xItem, Pointer.reduction xp (yp::yP.append xP)⟩
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
    (newBin : List (BinItem T N)) : CachedEarleyBins T N n :=
  Vector.modify bins k (fun x => updateBinCached x newBin)

end WellFormedBin

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinCached {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : CachedEarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : EarleyBins.WF G (rawList bins)) : WfEarleyBinsCached G w.size :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].raw.size then
    ⟨bins, hbins⟩
  else
    let x := bins[k].raw[j]
    let bins' := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A k
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
    have : EarleyBins.WF G (rawList bins') := by sorry
    earleyBinCached bins' k (by omega) (j+1) this
termination_by { x | isWellFormed G.rules w.size x }.ncard + 1 - j
decreasing_by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules w.size x }
    have : (items (rawList bins)[k]).length ≤ wfItemsBin.ncard := by
      have hF := Earley.Proofs.Finiteness.finiteEarleyWF G w.size
      have ⟨hNoDup, _, _, _⟩ := hbins
      let P := (fun x => isWellFormed G.rules w.size x)
      apply length_lte_ncard_of_superset (items (rawList bins)[k]) wfItemsBin P
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
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) :
    WfEarleyBinsCached G w.size :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  let bins := Vector.replicate (w.size + 1) ⟨Array.empty,  {},  {}⟩
  let bins' := updateBinsCached bins 0 (initList G)
  have : EarleyBins.WF G (rawList bins') := by
    have := G.nodup
    simp only [EarleyBins.WF, Order.lt_add_one_iff]
    intro k hk
    if hk : k = 0 then
      sorry
    else
      --grind [initList]
      sorry
  ⟨bins', this⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsCached (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (h : k < w.size + 1) : WfEarleyBinsCached G w.size :=
  match h : k with
  | 0 =>
    let ⟨bins, inv⟩ := initCachedBins G w
    earleyBinCached bins 0 (by simp) 0 inv
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let ⟨bins, inv⟩ := earleyBinsCached G w i (by lia)
    earleyBinCached bins k (by lia) 0 inv

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyCached (G : ContextFreeGrammarList T N) (w : Array T) :
    WfEarleyBinsCached G w.size :=
  earleyBinsCached G w w.size (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) [LawfulBEq T] : Bool :=
  let bins := earleyCached G w |>.bins
  let finalItems := itemsA bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end CachedRecognizerPointers
end Earley
