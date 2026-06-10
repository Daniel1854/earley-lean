module
public import Earley.Model
public import Earley.Limit
@[expose] public section

/-!
This module represents a fixpoint implementation of the Earley algorithm.
It's a stepping stone to refine from the inductive definition to the fully functional one.

TODO: Set (EarleyItems) - how does it differ from the Model? Where does it help?
      It simply describes a set of items and not how to construct them inductively I suppose
      but through sheer application of operations? The technical difference seems quite low
      But maybe there is some relation to the bins that helps!
-/

namespace Earley
namespace Fixpoint

open Model
open EarleyItem

variable {T N : Type} [BEq N]

/--
Returns the subset of `I` where endIdx is equal to `k`.
Corresponds to the i-th bin in the list-based algorithm.
-/
def bin (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { x ∈ I | x.endIdx = k }

/--
Set-based implementation of the .init operation.
-/
def initFixpoint (G : ContextFreeGrammar T) : Set (EarleyItem T G.NT) :=
  { ⟨r,pos,i,j⟩ | pos = 0 ∧ i = 0 ∧ j = 0 ∧ (r ∈ G.rules) ∧ r.input = G.initial }

/--
Set-based implementation of the .scan operation.

TODO: a bit annoying that I have to do w[k]? since the previous assumption is the bounds check
-/
def scanFixpoint (I : Set (EarleyItem T N)) (w : List (Symbol T N)) (k : Nat) :
      Set (EarleyItem T N) :=
  { y | ∀ x a, y = incItem x (k+1) ∧ x ∈ bin I k ∧
    k < w.length ∧ w[k]? = some a ∧ nextSymbol x = some a }

/--
Set-based implementation of the .predict operation.
-/
def predictFixpoint (G : ContextFreeGrammar T) (I : Set (EarleyItem T G.NT)) (k : Nat) :
    Set (EarleyItem T G.NT) :=
  { ⟨r,pos,i,j⟩ | ∀ x, pos = 0 ∧ i = 0 ∧ j = 0 ∧
    (r ∈ G.rules) ∧ x ∈ bin I k ∧ nextSymbol x = some (Symbol.nonterminal r.input) }

/--
Set-based implementation of the .complete operation.
-/
def completeFixpoint (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { z | ∀ x y : EarleyItem T N, z = incItem x k ∧ x ∈ bin I y.startIdx ∧
    y ∈ bin I k ∧ isComplete y ∧ nextSymbol x = some (Symbol.nonterminal y.rule.input) }

/--
One step of the fixpoint iteration.
-/
def earleyFixpointBinStep (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  I ∪ scanFixpoint I w k ∪ completeFixpoint I k ∪ predictFixpoint G I k

/--
Fixpoint Iteration of a single bin.
-/
def earleyFixpointBin (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  Limit.limit (earleyFixpointBinStep G w k) I

/--
Set-based computation up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
def earleyFixpointBins (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (k : Nat) :
    Set (EarleyItem T G.NT) :=
  match k with
  | 0 => earleyFixpointBin G w 0 (initFixpoint G)
  | n+1 => earleyFixpointBin G w (n+1) (earleyFixpointBins G w n)

/--
Set-based/fixpoint iteration based computation of the EarleySet.
-/
def earleyFixpoint (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) :
    Set (EarleyItem T G.NT) :=
  earleyFixpointBins G w w.length

end Fixpoint
end Earley
