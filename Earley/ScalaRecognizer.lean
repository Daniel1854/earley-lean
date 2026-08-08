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
This module represents a computable implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to `Recognizer`, this implementation follows the algorithmic choices
from Rau et Nipkow (https://doi.org/10.4230/LIPIcs.ITP.2024.31) fully.
In particular:
- The input word is a linked list instead of an Array
- The Bins are a 2D Linked List instead of a Vector of a Linked List
- updateBinAux: more expensive matching
- completeList: adds another traversal of the full list to map onto item before filtering

This is simply a dummy implementation to compare performance without proofs,
relying on `Inhabited` for list accesses.
-/

@[expose] public section

namespace Earley
namespace ScalaRecognizer

open Model
open EarleyItem
open Utils
open Recognizer

deriving instance Inhabited for ContextFreeRule
deriving instance Inhabited for EarleyItem
deriving instance Inhabited for Pointer
deriving instance Inhabited for BinItem

abbrev BinItems (T N : Type) : Type :=
  List (BinItem T N)

/--
Abbreviation for a two-dimensional list.
Outer list corresponds to the different positions for the word,
inner list corresponds to the items of that specific position.
-/
abbrev EarleyBins (T N : Type) : Type :=
  List (BinItems T N)

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] [Inhabited (BinItem T N)]

@[grind]
def items (bin : BinItems T N) : List (EarleyItem T N) :=
  bin.map (fun x => x.item)

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
public def completeList (y : EarleyItem T N) (bins : EarleyBins T N) (j : Nat) : BinItems T N :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := filterWithIdx (items bins[y.startIdx]!)
    (fun x => nextSymbol x == some (Symbol.nonterminal y.rule.input))
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

/--
Returns the list appended with an element, if it is not already part of the list,
while also merging any reduction pointers for duplicate items.
Predecessor pointers are unique, so duplicate items can be safely discarded
-/
@[inline]
public def updateBinAux :  BinItem T N  → BinItems T N → BinItems T N
  | y, [] => [y]
  | y, x::xs => match (x,y) with
    | (⟨xItem, Pointer.reduction xp xP⟩,⟨yItem, Pointer.reduction yp yP⟩) =>
      -- Merge any reduction pointers if the items match
      if xItem == yItem then
        ⟨yItem, Pointer.reduction xp (yp::yP.append xP)⟩::xs
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
@[inline]
public def updateBin (xs : BinItems T N) : BinItems T N → BinItems T N
  | [] => xs
  | y::ys => updateBin (updateBinAux y xs) ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
public def updateBins (bins : EarleyBins T N) (k : Nat) (newBin : BinItems T N) : EarleyBins T N  :=
  List.modify bins k (fun x => updateBin x newBin)

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public partial def earleyBinList (G : ContextFreeGrammarList T N) (w : List T)
    (bins : EarleyBins T N) (k : Nat) (j : Nat) : EarleyBins T N :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k]!.length then
    bins
  else
    let x := bins[k]![j]!
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
      let newItems := completeList x.item bins j
      updateBins bins k newItems
    earleyBinList G w bins' k (j+1)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initBins (G : ContextFreeGrammarList T N) (w : List T) : EarleyBins T N :=
  let b₀ := initList G
  let bins := List.replicate (w.length + 1) []
  bins.set 0 b₀

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (h : k < w.length + 1) : EarleyBins T N :=
  match h : k with
  | 0 =>
    let bins := initBins G w
    earleyBinList G w bins 0 0
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let bins := earleyBinsList G w i (by lia)
    earleyBinList G w bins k 0

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
public def earleyList (G : ContextFreeGrammarList T N) (w : List T) : EarleyBins T N :=
  earleyBinsList G w w.length (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) [LawfulBEq T] : Bool :=
  let bins := earleyList G w
  let finalItems := items bins[w.length]!
  ∃ x ∈ finalItems, isFinished G.initial w.length x

end ScalaRecognizer
end Earley
