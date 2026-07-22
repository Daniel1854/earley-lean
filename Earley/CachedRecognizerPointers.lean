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

In comparison to the cached implementation in `CachedRecognizer`, it maintains pointers
to reconstruct a parse tree afterwards. This is simply a dummy implementation.

These optimizations do make it such that maintaining only origin information per binitem would be
way more convenient, and since the implementation for `build_tree` only uses the first pointer
of the reduction pointer anyway, this isn't a big deal.
So maybe that would be a more appropriate next step?

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

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (Recognizer.BinItem T N)
  items : ItemCache T N
  completions : CompletionCache T N

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [BEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)]

@[grind]
def items (bin : Array (Recognizer.BinItem T N)) : Array (EarleyItem T N) :=
  bin.map (fun x => x.item)

section WellFormedBin

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
CachedEarleyBins are well-formed, if all of its bins and its caches are well-formed.
-/
@[grind]
public def isWellFormedCachedBins (G : ContextFreeGrammarList T N) (w : Array T)
    (bins : CachedEarleyBins T N (w.size + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → Recognizer.isWellFormedBinItems G w.toList k bins[k].raw.toList
    --∧ isWellFormedBinPointers w bins bins[k].raw k
    --∧ ∀ j, (hj : j < bins[k].raw.size) → Recognizer.isSoundPointer bins[k].raw[j].pointer k j
    --∧ sorry

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (w : Array T) where
  bins : CachedEarleyBins T N (w.size + 1)
  inv : isWellFormedCachedBins G w bins

public def scanList (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
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
public def completeCachedList (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : List (Recognizer.BinItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Recognizer.Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBin (bin : CachedEarleyBin T N) :
    List (Recognizer.BinItem T N) → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      have : idx < bin.raw.size := by sorry -- some wf cache argument
      match (bin.raw[idx], y) with
      | (⟨xItem, Recognizer.Pointer.reduction xp xP⟩,
          ⟨yItem, Recognizer.Pointer.reduction yp yP⟩) =>
        let updItem := ⟨xItem, Recognizer.Pointer.reduction xp (yp::xP.append yP)⟩
        updateBin { bin with raw := (bin.raw.swapAt idx updItem this).snd } ys
      | _ => updateBin bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y.item bin.raw.size
      match y.item.nextSymbol with
      | some (Symbol.nonterminal n) =>
        let completions' := bin.completions.alter n (fun zs => match zs with
          | some zs => zs.append [⟨y.item, bin.raw.size⟩]
          | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))
        updateBin ⟨raw', items', completions'⟩ ys
      | _ =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        updateBin ⟨raw', items', bin.completions⟩ ys

/--
FIXME: this searches for a place. A bit weird that it is not part of core.
-/
@[inline]
def modify {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

/--
Replace `bins` at index `k` with `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : List (Recognizer.BinItem T N)) : CachedEarleyBins T N n :=
  modify bins k (fun x => updateBin x newBin)

end WellFormedBin

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinList {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : CachedEarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : isWellFormedCachedBins G w bins) : WfEarleyBinsCached G w :=
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
          let newItem := scanList w x.item a k (by omega) j
          updateBinsCached bins (k+1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCachedList x.item bins (by sorry) j
      updateBinsCached bins k newItems
    have : isWellFormedCachedBins G w bins' := by sorry
    earleyBinList bins' k (by omega) (j+1) this
termination_by { x | isWellFormed G.rules (mapT w.toList) x }.ncard + 1 - j
decreasing_by --exact decreasingAux hbins j k (by lia) (by lia)
  sorry

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
TODO: I could use of Std.HashSet.ofList and something more clever for the HashMap cache,
      but utilizing updateBin is easier to reason with. It shouldnt be much worse perf-wise
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) : WfEarleyBinsCached G w :=
  let bins := Vector.replicate (w.size + 1) ⟨Array.empty,  {},  {}⟩
  let bins' := updateBinsCached bins 0 (Recognizer.initList G)
  ⟨bins', sorry⟩

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
  let finalItems := bins[w.size].raw.map (fun x => x.item)
  ∃ x ∈ finalItems, isFinished G.initial (mapT w.toList) x

end CachedRecognizerPointers
end Earley
