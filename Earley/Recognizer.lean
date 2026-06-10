module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Fixpoint
public import Earley.Filter
@[expose] public section

/-!
This module represents a functional implementation of the Earley algorithm.

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

TODO: Think if there are any issues arising from the input word being simply `List T`?
TODO: Think about the bins and how to make checking for membership efficient
      There still has to be an order, and I need an index for the parse tree
TODO: Think about how to prepare the grammar itself for efficient usage
      HashMap NT → List of rules ?
TODO: there is potential for early returns
-/

namespace Earley
namespace Recognizer

open Model
open EarleyItem
open Fixpoint
open Utils

/--
Variant of `ContextFreeGrammar` that uses a List internally to store the rules.
Context-free grammar that generates words over the alphabet `T` (a type of terminals).
-/
structure ContextFreeGrammarList (T N : Type) where
  /-- Initial nonterminal. -/
  initial : N
  /-- Rewrite rules. -/
  rules : List (ContextFreeRule T N)
  /-- `rules` contains no duplicates -/
  nodup : List.Nodup rules

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
  /--
  `endIdx` of the original item.
  -/
  endIdxA : Nat
  /--
  Index of the original item within its bin.
  -/
  i : Nat
  /--
  Index of the completed item within its bin.
  -/
  j : Nat
deriving BEq, Repr

/--
A Pointer helps keep track of the origin of an EarleyItem.
These are only required to assemble the parse tree after the successful recognition.
-/
inductive Pointer where
  /--
  .init/.predict: no origin data needed.
  -/
  | null : Pointer
  /--
  .scan: origin index for previous bin.
  -/
  | predecessor (i : Nat) : Pointer
  /--
  .complete: nonempty list of possible reduction pointers
  -/
  | reduction (ps : List ReductionPointer) : Pointer
deriving BEq, Repr

/--
The items of a bin. It contains the EarleyItem and data for its origin.
-/
public structure BinItem (T N : Type) where
  /--
  The EarleyItem of the item.
  -/
  item : EarleyItem T N
  /--
  The origin data of the item.
  -/
  pointer : Pointer
deriving BEq, Repr

/--
Abbreviation for a two-dimensional list.
Outer list corresponds to the different positions for the word,
inner list corresponds to the items of that specific position.

TODO: inner list should probably be an Array as well, but lets see first
-/
abbrev EarleyBins (T N : Type) (n : Nat) : Type :=
  Vector (List (BinItem T N)) n

variable {T N : Type} [BEq T] [BEq N]

/--
Returns if the grammar contains a rule with an empty rhs.
-/
def isEpsilonFree (G : ContextFreeGrammarList T N) : Prop :=
  ∀ r ∈ G.rules, !r.output.isEmpty

/--
An EarleyBin is well-formed, if
- there are no duplicate items in the bin
- all items in the bin are well-formed
- all endIdx match the index of the bin
-/
@[grind]
public def isWellFormedBin (G : ContextFreeGrammarList T N) (w : List (Symbol T N)) (k : Nat)
    (bin : List (BinItem T N)) : Prop :=
  bin.Nodup ∧ ∀ x ∈ bin, isWellFormed G.rules w x.item ∧ x.item.endIdx = k

/--
EarleyBins are well-formed, if all of its bins are well-formed.
-/
@[grind]
public def isWellFormedBins (G : ContextFreeGrammarList T N) (w : List (Symbol T N))
    (bins : EarleyBins T N (w.length + 1)) : Prop :=
  ∀ k, (h : k < bins.size) → isWellFormedBin G w k bins[k]

/--
List-based implementation of the .init operation.
Returns a list filled with all possible .init states.
-/
def initList (G : ContextFreeGrammarList T N) : List (BinItem T N) :=
  let rules := G.rules.filter (fun r => r.input == G.initial)
  rules.map (fun r => ⟨⟨r,0,0,0⟩, Pointer.null⟩)

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
TODO: Think about if Option is more sensible.
      This maybe makes sense if I dont switch to Arrays for the inner (expensive append)
-/
def scanList (w : List T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.length) (pre : Nat) :
    List (BinItem T N) :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Pointer.predecessor pre⟩]
  else
    []

/--
List-based implementation of the .predict operation.

Returns a fresh item for each rule, which got `A` as its lhs.
-/
def predictList (G : ContextFreeGrammarList T N) (A : N) (k : Nat) :
    List (BinItem T N) :=
  let rules := G.rules.filter (fun r => r.input == A)
  rules.map (fun r => ⟨⟨r,0,k,k⟩, Pointer.null⟩)

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
def completeList (y : BinItem T N) (n : Nat) (bins : EarleyBins T N n) (h : y.item.startIdx < n)
    (j : Nat) : List (BinItem T N) :=
  -- The full origin bin for potential completions
  let xBin := bins[y.item.startIdx]
  -- The origin bin filtered for matchings with y
  let xMatches : List (BinItem T N × Nat) := filterWithIdx xBin
    (fun x => nextSymbol x.item == some (Symbol.nonterminal y.item.rule.input))
  xMatches.map (fun ⟨x,i⟩ =>
    ⟨incItem x.item y.item.endIdx, Pointer.reduction [⟨y.item.startIdx,i,j⟩]⟩)

/--
Returns the list appended with an element, if it is not already part of the list,
while also merging any reduction pointers for duplicate items.
Predecessor pointers are unique, so duplicate items can be safely discarded
-/
@[inline, grind]
def updateBinAux : List (BinItem T N) → BinItem T N → List (BinItem T N)
  | [], y => [y]
  | x::xs, y => match (x,y) with
    | (⟨xItem, Pointer.reduction xP⟩,⟨yItem, Pointer.reduction yP⟩) =>
      -- Merge any reduction pointers if the items match
      if xItem == yItem then
        ⟨xItem, Pointer.reduction (xP.append yP)⟩::xs
      else
        -- Search further, if no match
        x::(updateBinAux xs y)
    | _ =>
      -- Abort, if an item with an irrelevant pointer already exists in the List
      if x.item == y.item then
        x::xs
      else
        -- Search further, if no match
        x::(updateBinAux xs y)

/--
Add given list one by one into `xs`, if they are not already part of `xs`,
while also merging any reduction pointers.
-/
@[inline, grind]
def updateBin (xs : List (BinItem T N)) : List (BinItem T N) → List (BinItem T N)
  | [] => xs
  | y::ys => updateBin (updateBinAux xs y) ys

/--
Computes the k-th bin starting from index j and returns the updated bins.
TODO: termination_by - Need to showcase (and know how to even write) that
      any element part of a bin is WF and there is only a finite amount of those.
-/
public partial def earleyBinList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (bins : EarleyBins T N (w.length + 1)) (h : k < bins.size) (j : Nat) :
    EarleyBins T N (w.length + 1) :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].length then
    bins
  else
    let x := bins[k][j]
    let bins' := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A k
        let newBin := updateBin bins[k] newItems
        bins.set k newBin (by grind)
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.length then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanList w x.item a k (by grind) j
          let newBin := updateBin bins[k+1] newItem
          bins.set (k+1) newBin (by grind)
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      have : x.item.startIdx < w.length + 1 := by
        -- TODO: In theory I only need to rely on the result that the bins only contain WF Items
        --       but this is a result _about_ this function so I cant access it ?
        --       Alternatively, I could parametrize the function with a proof that only wf items
        --       reside in the bins, but this makes everything a little convoluted?
        sorry
      let newItems := completeList x (w.length + 1) bins this j
      let newBin := updateBin bins[k] newItems
      bins.set k newBin ((by grind))
    earleyBinList G w k bins' (by grind) (j+1)

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (h : k ≤ w.length) : EarleyBins T N (w.length + 1) :=
  match h : k with
  | 0 =>
    -- Initialize the first bin by using .init for all G.rules
    let b₀ := initList G
    let bins := Vector.replicate (w.length + 1) []
    earleyBinList G w 0 (bins.set 0 b₀ (by grind)) (by grind) 0
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let mBins := earleyBinsList G w i (by grind)
    earleyBinList G w k mBins (by grind) 0

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
public def earleyList (G : ContextFreeGrammarList T N) (w : List T) :
    EarleyBins T N (w.length+1) :=
  earleyBinsList G w w.length (by grind)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ Array ?
-/
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) : Bool :=
  let bins := earleyList G w
  ∃ x ∈ bins[w.length], isFinished G.initial (w.map Symbol.terminal) x.item

end Recognizer
end Earley
