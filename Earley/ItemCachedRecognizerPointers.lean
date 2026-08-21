/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Filter
public import Earley.Recognizer

/-!
This module represents an optimized implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to the implementation in `CachedRecognizerPointers`, this version only utilizes
an ItemCache and no CompletionCache.
This is simply a dummy implementation to compare performance without proofs,
relying on `Inhabited` for array/hashmap accesses.
-/

@[expose] public section

namespace Earley
namespace ItemCachedRecognizerPointers

open Model
open EarleyItem
open Utils
open Recognizer

deriving instance Inhabited for ContextFreeRule
deriving instance Inhabited for EarleyItem
deriving instance Inhabited for Pointer
deriving instance Inhabited for BinItem

@[grind]
def itemsA {T N : Type} (bin : Array (BinItem T N)) : Array (EarleyItem T N) :=
  bin.map (fun x => x.item)

/--
A cache for checking if an items resides within a single bin.
Maps an EarleyItem to its index within the bin.
-/
abbrev ItemCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] : Type :=
  Std.HashMap (EarleyItem T N) Nat

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (BinItem T N)
  items : ItemCache T N
deriving Inhabited

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)] [Inhabited (BinItem T N)]

@[grind]
def rawList {n : Nat} (bins : CachedEarleyBins T N n) : EarleyBins T N n :=
  bins.map (fun x => x.raw.toList)

public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n) (j : Nat) :
    BinItems T N :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (BinItem T N × Nat) := filterWithIdx bins[y.startIdx]!.raw.toList
    (fun x => nextSymbol x.item == some (Symbol.nonterminal y.rule.input))
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x.item y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBinCached (bin : CachedEarleyBin T N) : BinItems T N → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      match (bin.raw[idx]!.pointer, y.pointer) with
      | (Pointer.reduction xp xP, Pointer.reduction yp yP) =>
        let updItem : BinItem T N := ⟨y.item, Pointer.reduction xp (yp::yP.append xP)⟩
        let newBin := ⟨bin.raw.set! idx updItem, bin.items⟩
        updateBinCached newBin ys
      | _ => updateBinCached bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y.item bin.raw.size
      updateBinCached ⟨raw', items'⟩ ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : BinItems T N) : CachedEarleyBins T N n :=
  Vector.modify bins k (fun x => updateBinCached x newBin)

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public partial def earleyBinCached (G : ContextFreeGrammarList T N) {w : Array T}
    (bins : CachedEarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat) :
    CachedEarleyBins T N (w.size + 1) :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].raw.size then
    bins
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
          let newItem := scanList w x.item a k (by omega) j
          updateBinsCached bins (k + 1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCached x.item bins j
      updateBinsCached bins k newItems
    earleyBinCached G bins' k (by omega) (j+1)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) :
    CachedEarleyBins T N (w.size + 1) :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  let bins := Vector.replicate (w.size + 1) ⟨.empty,  {}⟩
  updateBinsCached bins 0 (initList G)

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsCached (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (h : k < w.size + 1) : CachedEarleyBins T N (w.size + 1) :=
  match h : k with
  | 0 =>
    let bins := initCachedBins G w
    earleyBinCached G bins 0 (by simp) 0
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let bins := earleyBinsCached G w i (by lia)
    earleyBinCached G bins k (by lia) 0

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyCached (G : ContextFreeGrammarList T N) (w : Array T) :
    CachedEarleyBins T N (w.size + 1) :=
  earleyBinsCached G w w.size (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.
-/
@[grind]
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) : Bool :=
  let bins := earleyCached G w
  let finalItems := itemsA bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end ItemCachedRecognizerPointers
end Earley
