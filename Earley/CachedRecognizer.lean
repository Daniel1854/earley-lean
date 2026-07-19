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
This module represents a optimized implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to the naive implementation in `Recognizer`:
- caches if an item already exists in a bin
- caches the indices for the items that can be completed: HashMap N (i, EarleyItem T N)
- doesn't maintain pointers to reconstruct a parse tree afterwards

These optimizations do make it such that maintaining only origin information per binitem would be
way more convenient, and since the implementation for `build_tree` only uses the first pointer
of the reduction pointer anyway, this isn't a big deal. So extending to that makes somewhat sense?

TODO: CachedParser would use `Array.findIdx?` instead of filterWithIdx?
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
Maps a non-terminal to all the EarleyItems that the bin contains for it and
their index within the bin.
-/
abbrev CompletionCache (T N : Type) [BEq N] [Hashable N] : Type :=
  Std.HashMap N (List (EarleyItem T N × Nat))

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (EarleyItem T N)
  items : ItemCache T N
  completions : CompletionCache T N

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)]

--@[grind]
--def items (bin : Array (Recognizer.BinItem T N)) : Array (EarleyItem T N) :=
--  bin.map (fun x => x.item)

section WellFormedBin

-- FIXME: I dont merge, so maybe I need less of the invariant?
--@[grind]
--public def isWellFormedPointer (w : List T) (bins : CachedEarleyBins T N (w.length + 1))
--    (pointer : Recognizer.Pointer) (k : Nat) : Prop :=
--  match pointer with
--  | .null => True
--  | .predecessor i => k ≠ 0 ∧ k - 1 ≤ w.length ∧ ((h : k - 1 ≤ w.length) → i < bins[k-1].raw.size)
--  | .reduction p ps => k ≤ w.length ∧ p.endIdxA ≤ w.length ∧
--      ((h : p.endIdxA ≤ w.length) → p.i < bins[p.endIdxA].raw.size) ∧
--      ((h : k ≤ w.length) → p.j < bins[k].raw.size)
--
--@[grind]
--public def isWellFormedBinPointers (w : List T) (bins : CachedEarleyBins T N (w.length + 1))
--    (bin : Array (Recognizer.BinItem T N)) (k : Nat) : Prop :=
--  ∀ x ∈ bin, isWellFormedPointer w bins x.pointer k

/--
The items of an EarleyBin are well-formed, if
- there are no duplicate items in the bin
- all items in the bin are well-formed
- the endIdx of all items match the index of the bin
-/
@[grind]
public def isWellFormedBinItems (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (bin : Array (EarleyItem T N)) : Prop :=
  bin.toList.Nodup ∧ ∀ x ∈ bin, isWellFormed G.rules (mapT w) x ∧ x.endIdx = k

/--
CachedEarleyBins are well-formed, if all of its bins and its caches are well-formed.
FIXME: missing pointer invariants
-/
@[grind]
public def isWellFormedCachedBins (G : ContextFreeGrammarList T N) (w : List T)
    (bins : CachedEarleyBins T N (w.length + 1)) : Prop :=
  -- FIXME: missing invariant about the cache stating that the items correspond
  --        to the items in each bin ? Or do I want to prove this separately?
  ∀ k, (hk : k < bins.size) → isWellFormedBinItems G w k bins[k].raw
    --∧ sorry

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (w : List T) where
  bins : CachedEarleyBins T N (w.length + 1)
  inv : isWellFormedCachedBins G w bins

/--
List-based implementation of the .init operation.
Returns a list filled with all possible .init states.
-/
public def initCached (G : ContextFreeGrammarList T N) : List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == G.initial)
  rules.map (fun r => ⟨r,0,0,0⟩)

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
-/
public def scanCached (w : List T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.length) :
    List (EarleyItem T N) :=
  if w[k] == a then
    [incItem x (x.endIdx+1)]
  else
    []

/--
List-based implementation of the .predict operation.

Returns a fresh item for each rule, which got `A` as its lhs.
-/
public def predictCached (G : ContextFreeGrammarList T N) (A : N) (k : Nat) :
    List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == A)
  rules.map (fun r => ⟨r,0,k,k⟩)

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
-/
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) : List (EarleyItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => incItem x y.endIdx)

/--
Add given list one by one into `xs`, if they are not already part of `xs`.
-/
@[inline, grind]
public def updateBin (xs : CachedEarleyBin T N) : List (EarleyItem T N) → CachedEarleyBin T N
  | [] => xs
  | y::ys =>
    if xs.items.contains y then
      updateBin xs ys
    else
      let raw' := xs.raw ++ [y]
      let items' :=  xs.items.insert y
      match y.nextSymbol with
      | some (Symbol.nonterminal n) =>
        match xs.completions[n]? with
        | some _ =>
          -- There exists an entry: append the list with the item of y
          updateBin ⟨raw', items', xs.completions.modify n
            (fun zs => zs.append [⟨y, xs.raw.size⟩])⟩ ys
        | none =>
          -- No entry for `n` yet: create new list for `n` with `y` as first elem.
          updateBin ⟨raw', items', xs.completions.insert n [⟨y, xs.raw.size⟩]⟩ ys
      | _ =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        updateBin ⟨raw', items', xs.completions⟩ ys

/--
Replace `bins` at index `k` with `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat) (hk : k < n)
    (newBin : List (EarleyItem T N)) : CachedEarleyBins T N n :=
  let updBin := updateBin bins[k] newBin
  bins.set k updBin hk


omit [LawfulBEq (EarleyItem T N)] in
public theorem startIdx_of_Wf {G : ContextFreeGrammarList T N} {w : List T} (x : EarleyItem T N)
    {bins : CachedEarleyBins T N (w.length + 1)} (hbins : isWellFormedCachedBins G w bins)
    (k : Nat) (hk : k < w.length + 1) (j : Nat) (hj : j < bins[k].raw.size)
    (hmemx : x = bins[k].raw[j]) : x.startIdx < w.length + 1 := by
  have : x ∈ bins[k].raw := by grind
  grind

end WellFormedBin

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList {G : ContextFreeGrammarList T N} {w : List T}
    (bins : CachedEarleyBins T N (w.length + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : isWellFormedCachedBins G w bins) : WfEarleyBinsCached G w :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].raw.size then
    ⟨bins, hbins⟩
  else
    let x := bins[k].raw[j]
    let bins' := match nextSymbol x with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictCached G A k
        updateBinsCached bins k hk newItems
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.length then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanCached w x a k (by omega)
          updateBinsCached bins (k+1) (by lia) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCached x bins (by grind [startIdx_of_Wf x hbins])
      updateBinsCached bins k hk newItems
    have : isWellFormedCachedBins G w bins' := by sorry
    earleyBinList bins' k (by omega) (j+1) this
termination_by { x | isWellFormed G.rules (mapT w) x }.ncard + 1 - j
decreasing_by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules (mapT w) x }
    have : bins[k].raw.size ≤ wfItemsBin.ncard := by
      have hF := Earley.Proofs.Finiteness.finiteEarleyWF G (mapT w)
      let P := (fun x => isWellFormed G.rules (mapT w) x)
      apply Recognizer.length_lte_ncard_of_superset bins[k].raw.toList wfItemsBin P
        (by grind) (by grind) hbins.left
    grind
  · simp

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
TODO: I could use of Std.HashSet.ofList and something more clever for the HashMap cache,
      but utilizing updateBin is easier to reason with. It shouldnt be much worse perf-wise
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBinsCached G w :=
  let bins : Vector (CachedEarleyBin T N) (w.length + 1) :=
    Vector.replicate (w.length + 1) ⟨Array.empty,  {},  {}⟩
  let bins' := updateBinsCached bins 0 (by lia) (initCached G)
  ⟨bins', (by sorry)⟩ --grind [initList, wfBinItems_of_initList])⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (h : k < w.length + 1) : WfEarleyBinsCached G w :=
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
public def earleyList (G : ContextFreeGrammarList T N) (w : List T) : WfEarleyBinsCached G w :=
  earleyBinsList G w w.length (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w |>.bins
  let finalItems := bins[w.length].raw
  ∃ x ∈ finalItems, isFinished G.initial (mapT w) x

end CachedRecognizer
end Earley
