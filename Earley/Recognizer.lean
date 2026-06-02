module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Fixpoint
@[expose] public section

/-!
This module represents a functional implementation of the Earley algorithm.

Given an input word `w = a_0 .. a_(n-1)` of length `n`, we maintain a list of `n+1` bins `B_i`.
For the initial starting position and position after parsing a certain characters,
we maintain a bin of the possible states we could be in.
Each bin contains a set of Earley Entries, which are a pair of an Earley Item and indices,
which help us keep track of its origin. These are only required to assemble the parse tree.

These indices are either
- init/predict: null/⊥
- scan: a predecessor pointer via one index `i`
- completion: nonempty list of triple indices `(j,l',l)`, where
  - j is the endIdx of the original item and l' is its index within bin_j
  - l is the index for the completeable item within the current bin

The endindex of an EarleyItem corresponds always to the bin number.
`B_0` is filled with the items from the INIT rule

The parse tree will only be built _after_ a word has been fully recognized,
thus the Recognizer has to keep track of all its bins until its done.

The algorithm goes through the bins in ascending order.
Due to a complication with epsilon rules, `.complete` may miss transitions,
so Rau only reasons about epsilon free grammars.

The implementation and its proofs follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31

TODO: As of now we only keep track of the Earley Item and let the Parse Tree be a future worry.
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

/--
Abbreviation for a two-dimensional list.
Outer list corresponds to the different positions for the word,
inner list corresponds to the items of that specific position.

TODO: abbrev makes sense here right? Since I do want it to be comparable?
TODO: inner list should probably be an Array as well, but lets see first
-/
abbrev EarleyBins (T : Type) (N : Type) (n : Nat) : Type := Vector (List (EarleyItem T N)) n

variable {T : Type} {N : Type} [BEq T] [BEq N]

/--
List-based implementation of the .init operation.
Returns a list filled with all possible .init states.
-/
def initList (G : ContextFreeGrammarList T N) : List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == G.initial)
  rules.map (fun r => ⟨r,0,0,0⟩)

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `i`.
TODO: Think about if Option is more sensible.
      This maybe makes sense if I dont switch to Arrays for the inner (expensive append)
-/
def scanList (w : List T) (x : EarleyItem T N) (a : T) (i : Nat) (h : i < w.length) :
    List (EarleyItem T N) :=
  if w[i] == a then
    [incItem x x.endItem]
  else
    []

/--
List-based implementation of the .predict operation.

Returns a fresh item for each rule, which got `A` as its lhs.
-/
def predictList (G : ContextFreeGrammarList T N) (A : N) (i : Nat) :
    List (EarleyItem T N) :=
  let rules := G.rules.filter (fun r => r.input == A)
  rules.map (fun r => ⟨r,0,i,i⟩)

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startItem index for bins.

TODO: for the parse tree the filter needs to also keep track of the index within the original list
      Rau uses custom filter_with_index, we can use filterMap
TODO: completely unclear why Rau parametrizes k when it is already a part of y?
-/
def completeList (y : EarleyItem T N) (n : Nat) (bins : EarleyBins T N n) (h : y.startItem < n) :
    List (EarleyItem T N) :=
  -- The full origin bin for potential completions
  let xBin := bins[y.startItem]
  -- The origin bin filtered for matchings with y
  let xItems := xBin.filter (fun x => nextSymbol x == some (Symbol.nonterminal y.rule.input))
  xItems.map (fun x => incItem x y.endItem)

/--
Returns xs appended with the elements of ys, that are not part of xs.
TODO: .push would be so much nicer than .append :)
-/
@[inline, grind]
def appendNoDupl (xs : List (EarleyItem T N)) (ys : List (EarleyItem T N)) :
    List (EarleyItem T N) :=
  xs.append (ys.filter (fun y => !xs.contains y))

/--
Computes the i-th bin starting from index j and returns the updated bins.
TODO: termination_by - Need to showcase (and know how to even write) that
      any element part of a bin is WF and there is only a finite amount of those.
-/
public partial def earleyBinList (G : ContextFreeGrammarList T N) (w : List T) (i : Nat)
    (bins : EarleyBins T N (w.length + 1)) (hi : i < bins.size) (j : Nat) :
    EarleyBins T N (w.length + 1) :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[i].length then
    bins
  else
    let x := bins[i][j]
    let bins' := match nextSymbol x with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A i
        let newBin := appendNoDupl bins[i] newItems
        bins.set i newBin (by grind)
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hi : i ≥ w.length then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanList w x a i (by grind)
          let newBin := appendNoDupl bins[i] newItem
          bins.set (i+1) newBin (by grind)
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      have : x.startItem < w.length + 1 := by
        -- TODO: In theory I only need to rely on the result that the bins only contain WF Items
        --       but this a result _about_ this function so I cant access it ?
        --       Alternatively, I could parametrize the function with a proof that only wf items
        --       reside in the bins, but this makes everything a little convoluted?
        sorry
      let newItems := completeList x (w.length + 1) bins this
      let newBin := appendNoDupl bins[i] newItems
      bins.set i newBin ((by grind))
    earleyBinList G w i bins' (by grind) (j+1)

/--
Computes up to the i-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
public def earleyBinsList (G : ContextFreeGrammarList T N) (w : List T) (i : Nat)
    (hi : i ≤ w.length) : EarleyBins T N (w.length + 1) :=
  match h : i with
  | 0 =>
    -- Initialize the first bin by using .init for all G.rules
    let b₀ := initList G
    let bins := Vector.replicate (w.length + 1) []
    earleyBinList G w 0 (bins.set 0 b₀ (by grind)) (by grind) 0
  | j+1 =>
    -- Given the first mth bins being computed, we can compute m+1
    let mBins := earleyBinsList G w j (by grind)
    earleyBinList G w i mBins (by grind) 0

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ Array ?
-/
public def recognizeList (G : ContextFreeGrammarList T N) (w : List T) : Bool :=
  let bins := earleyBinsList G w w.length (by grind)
  ∃ x ∈ bins[w.length], isFinishedList G w x

-- FIXME: delete :)
public def recognizeTest (G : ContextFreeGrammarList T N) (w : List T) :
    EarleyBins T N (w.length+1) :=
  let bins := earleyBinsList G w w.length (by grind)
  bins

end Recognizer
end Earley
