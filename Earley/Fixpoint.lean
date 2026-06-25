/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Limit

/-!
This module represents a fixpoint implementation of the Earley algorithm.
It's a stepping stone to refine from the inductive definition to the fully functional one.

TODO: Set (EarleyItems) - how does it differ from the Model? Where does it help?
      It simply describes a set of items and not how to construct them inductively I suppose
      but through sheer application of operations? The technical difference seems quite low
      But maybe there is some relation to the bins that helps!
-/

@[expose] public section

namespace Earley
namespace Fixpoint

open Model
open EarleyItem

variable {T N : Type} [BEq N]

/--
Returns the subset of `I` where endIdx is equal to `k`.
Corresponds to the i-th bin in the list-based algorithm.
-/
@[grind]
def bin (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { x ∈ I | x.endIdx = k }

@[grind]
def initFixpoint (G : ContextFreeGrammar T) : Set (EarleyItem T G.NT) :=
  { x | ∃ r, x = ⟨r,0,0,0⟩ ∧ r ∈ G.rules ∧ r.input = G.initial }

-- TODO: a bit annoying that I have to do w[k]? since the previous assumption is the bounds check
@[grind]
def scanFixpoint (I : Set (EarleyItem T N)) (w : List (Symbol T N)) (k : Nat) :
      Set (EarleyItem T N) :=
  { y | ∃ x a, y = incItem x (k+1) ∧ x ∈ bin I k ∧
    k < w.length ∧ w[k]? = some a ∧ nextSymbol x = some a }

@[grind]
def predictFixpoint (G : ContextFreeGrammar T) (I : Set (EarleyItem T G.NT)) (k : Nat) :
    Set (EarleyItem T G.NT) :=
  { y | ∃ x r, y = ⟨r,0,k,k⟩ ∧ r ∈ G.rules ∧ x ∈ bin I k ∧
    nextSymbol x = some (Symbol.nonterminal r.input) }

@[grind]
def completeFixpoint (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { z | ∃ x y , z = incItem x k ∧ x ∈ bin I y.startIdx ∧
    y ∈ bin I k ∧ isComplete y ∧ nextSymbol x = some (Symbol.nonterminal y.rule.input) }

/--
One step of the fixpoint iteration.
-/
@[grind]
def earleyFixpointBinStep (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  I ∪ scanFixpoint I w k ∪ completeFixpoint I k ∪ predictFixpoint G I k

/--
Fixpoint Iteration of a single bin.
-/
@[grind]
def earleyFixpointBin (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  Limit.limit (earleyFixpointBinStep G w k) I

/--
Set-based computation up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
def earleyFixpointBins (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat) :
    Set (EarleyItem T G.NT) :=
  match k with
  | 0 => earleyFixpointBin G w 0 (initFixpoint G)
  | n+1 => earleyFixpointBin G w (n+1) (earleyFixpointBins G w n)

/--
Set-based/fixpoint iteration based computation of the EarleySet.
-/
@[grind]
def earleyFixpoint (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) :
    Set (EarleyItem T G.NT) :=
  earleyFixpointBins G w w.length

end Fixpoint
end Earley
