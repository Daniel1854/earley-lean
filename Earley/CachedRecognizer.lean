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

This is the cached variant. It adds:
- an index for the items in a bin, so checking for containment becomes O(1) HashSet (EarleyItem T N)
- maybe an index for the items that could be completed? HashMap N (i, BinItem T N)

These optimizations do make it such that maintaining only origin information per binitem is way
more convenient, and since the implementation for `build_tree` only uses the first pointer
of the reduction pointer anyway, this isn't a big deal.

TODO: the inner list as arrays would be very nice. If I can cache completion and
      remove filterWithIdx, this should be not that difficult?
-/

@[expose] public section

namespace Earley
namespace CachedRecognizer

open Model
open EarleyItem
open Utils
open Recognizer

/--
A cache for the items that are within a single bin.
-/
abbrev BinCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] : Type :=
  Std.HashSet (EarleyItem T N)

/--
A cache about the items of each bin.
-/
abbrev BinsCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (BinCache T N ) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable (EarleyItem T N)]

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
TODO: see if I should layer the struct
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (w : List T) where
  bins : EarleyBins T N (w.length + 1)
  inv : isWellFormedBins G w bins
  cache : BinsCache T N (w.length + 1)
  -- FIXME: missing invariant about the cache stating that the items correspond
  --        to the items in each bin

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def _completeList (y : EarleyItem T N) {n : Nat} (bins : EarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : List (BinItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (BinItem T N × Nat) := filterWithIdx bins[y.startIdx]
    (fun x => nextSymbol x.item == some (Symbol.nonterminal y.rule.input))
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x.item y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Add given list one by one into `xs`, if they are not already part of `xs`,
while also merging any reduction pointers.
-/
@[inline, grind]
public def updateBin (xs : List (BinItem T N)) (cache : BinCache T N) :
    List (BinItem T N) → List (BinItem T N) × BinCache T N
  | [] => ⟨xs, cache⟩
  | y::ys =>
    if cache.contains y.item then
      updateBin xs cache ys
    else
      updateBin (xs ++ [y]) (cache.insert y.item) ys

/--
Replace `bins` at index `k` with `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : EarleyBins T N n) (k : Nat)
    (newBin : List (BinItem T N)) (cache : BinsCache T N n) (hk : k < n) :
    EarleyBins T N n × BinsCache T N n :=
  let ⟨bin', cache'⟩ := updateBin bins[k] cache[k] newBin
  ⟨bins.set k bin' hk, cache.set k cache' hk⟩

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (bins : EarleyBins T N (w.length + 1)) (h : k < bins.size) (j : Nat)
    (hbins : isWellFormedBins G w bins) (cache : BinsCache T N (w.length + 1)) :
    WfEarleyBinsCached G w :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].length then
    ⟨bins, hbins, cache⟩
  else
    let x := bins[k][j]
    let ⟨bins', cache'⟩ := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A k
        updateBinsCached bins k newItems cache (by omega)
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.length then
          ⟨bins, cache⟩
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanList w x.item a k (by omega) j
          updateBinsCached bins (k+1) newItem cache (by omega)
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeList x.item bins (by grind) j
      updateBinsCached bins k newItems cache (by omega)
    have : isWellFormedBins G w bins' := by sorry
    earleyBinList G w k bins' (by omega) (j+1) this cache'
termination_by { x | isWellFormed G.rules (mapT w) x }.ncard + 1 - j
decreasing_by exact decreasingAux hbins j k (by lia) (by lia)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initBins (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBinsCached G w :=
  let b₀ := initList G
  let bins := Vector.replicate (w.length + 1) []
  let bins' := bins.set 0 b₀ (by simp)
  let cache : BinsCache T N (w.length + 1) := Vector.replicate (w.length + 1) {}
  let cache' := cache.set 0 (Std.HashSet.ofList (items b₀)) (by simp)
  ⟨bins', (by grind [initList, wfBinItems_of_initList]), cache'⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (h : k < w.length + 1) : WfEarleyBinsCached G w :=
  match h : k with
  | 0 =>
    let ⟨bins, inv, cache⟩ := initBins G w
    earleyBinList G w 0 bins (by simp) 0 inv cache
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let ⟨mBins, inv, cache⟩ := earleyBinsList G w i (by lia)
    earleyBinList G w k mBins (by lia) 0 inv cache

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyList (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBinsCached G w :=
  earleyBinsList G w w.length (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w |>.bins
  let finalItems := items bins[w.length]
  ∃ x ∈ finalItems, isFinished G.initial (mapT w) x

end CachedRecognizer
end Earley
