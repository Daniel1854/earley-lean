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

In comparison to the cached implementation in `CachedRecognizerPointers`, it doesn't maintain
pointers to reconstruct a parse tree afterwards.
This is simply a dummy implementation to compare performance without proofs,
relying on `Inhabited` for array/hashmap accesses.
-/

@[expose] public section

namespace Earley
namespace CachedRecognizer

open Model
open EarleyItem
open Utils

/--
A cache for checking if an items resides within a single bin.
-/
abbrev ItemCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] : Type :=
  Std.HashSet (EarleyItem T N)

/--
A cache for accessing the possible rules for a completion within a single bin.
Maps a non-terminal to all the EarleyItems that the bin contains for it.
-/
abbrev CompletionCache (T N : Type) [BEq N] [Hashable N] : Type :=
  Std.HashMap N (List (EarleyItem T N))

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (EarleyItem T N)
  items : ItemCache T N
  completions : CompletionCache T N
deriving Inhabited

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)]

/--
List-based implementation of the .init operation.
Returns a list filled with all possible .init states.
-/
@[inline]
public def initCached (G : ContextFreeGrammarList T N) : List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == G.initial)
  rules.map (fun r => ⟨r,0,0,0⟩)

/--
Equal to list-based implementation of the .scan operation,
but it takes an `Array T` as the input word.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
-/
@[inline]
public def scanCached (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size) :
    List (EarleyItem T N) :=
  if w[k] == a then
    [incItem x (x.endIdx+1)]
  else
    []

/--
Equal to list-based implementation of the .predict operation.

Returns a fresh item for each rule, which got `A` as its lhs.
-/
@[inline]
public def predictCached (G : ContextFreeGrammarList T N) (A : N) (k : Nat) :
    List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == A)
  rules.map (fun r => ⟨r,0,k,k⟩)

/--
Cached implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
-/
@[inline]
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n) :
    List (EarleyItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N) := bins[y.startIdx]!.completions.getD y.rule.input []
  -- Matchings mapped onto a new item
  xMatches.map (fun x => incItem x y.endIdx)

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[grind]
public def updateBinCached (bin : CachedEarleyBin T N) : List (EarleyItem T N) → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if bin.items.contains y then
      updateBinCached bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y
      match y.nextSymbol with
      | some (Symbol.nonterminal n) =>
        let completions' := bin.completions.alter n (fun zs => match zs with
          | some zs => zs.append [y]
          | none => [y])
        updateBinCached ⟨raw', items', completions'⟩ ys
      | _ =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        updateBinCached ⟨raw', items', bin.completions⟩ ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : List (EarleyItem T N)) : CachedEarleyBins T N n :=
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
    let bins' := match nextSymbol x with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictCached G A k
        updateBinsCached bins k newItems
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.size then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanCached w x a k (by omega)
          updateBinsCached bins (k+1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCached x bins
      updateBinsCached bins k newItems
    earleyBinCached G bins' k (by omega) (j+1)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
TODO: I could use of Std.HashSet.ofList and something more clever for the HashMap cache,
      but utilizing updateBin is easier to reason with. It shouldnt be much worse perf-wise
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) :
    CachedEarleyBins T N (w.size + 1) :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  let bins := Vector.replicate (w.size + 1) ⟨Array.empty,  {},  {}⟩
  updateBinsCached bins 0 (initCached G)

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
    earleyBinCached G bins 0 (by lia) 0
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
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) [LawfulBEq T] : Bool :=
  let bins := earleyCached G w
  let finalItems := bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end CachedRecognizer
end Earley
