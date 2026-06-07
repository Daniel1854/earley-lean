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
TODO: This set-based implementation doesn't _really_ need the CFGₗ BUT the refinement proof
      from EarleySet should be quite easy and the friction is better here than from
      EarleyFixpoint -> EarleySet?
      There is only one point where List vs. Finset is disruptive: `finiteEarleyNonEmpty`
      I could use .image.max' to select the rule with the longest output.
-/

namespace Earley
namespace Fixpoint

open Model
open EarleyItem

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

variable {T N : Type} [BEq N]

/--
Returns if the grammar contains a rule with an empty rhs.
-/
def isEpsilonFree (G : ContextFreeGrammarList T N) : Prop :=
  ∀ r ∈ G.rules, !r.output.isEmpty

/--
Returns the subset of `I` where endItem is equal to `k`.
Corresponds to the i-th bin in the list-based algorithm.
-/
def bin (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { x ∈ I | x.endItem = k }

/--
Set-based implementation of the .init operation.
-/
def initFixpoint (G : ContextFreeGrammarList T N) : Set (EarleyItem T N) :=
  { ⟨r,pos,i,j⟩ | pos = 0 ∧ i = 0 ∧ j = 0 ∧ (r ∈ G.rules) ∧ r.input = G.initial }

/--
Set-based implementation of the .scan operation.

TODO: a bit annoying that I have to do w[k]? since the previous assumption is the bounds check
-/
def scanFixpoint (I : Set (EarleyItem T N)) (w : List T) (k : Nat) :
      Set (EarleyItem T N) :=
  { y | ∀ x a, y = incItem x (k+1) ∧ x ∈ bin I k ∧
    k < w.length ∧ w[k]? = some a ∧ nextSymbol x = some (Symbol.terminal a) }

/--
Set-based implementation of the .predict operation.
-/
def predictFixpoint (G : ContextFreeGrammarList T N) (I : Set (EarleyItem T N)) (k : Nat) :
    Set (EarleyItem T N) :=
  { ⟨r,pos,i,j⟩ | ∀ x, pos = 0 ∧ i = 0 ∧ j = 0 ∧
    (r ∈ G.rules) ∧ x ∈ bin I k ∧ nextSymbol x = some (Symbol.nonterminal r.input) }

/--
Set-based implementation of the .complete operation.
-/
def completeFixpoint (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { z | ∀ x y : EarleyItem T N, z = incItem x k ∧ x ∈ bin I y.startItem ∧
    y ∈ bin I k ∧ isComplete y ∧ nextSymbol x = some (Symbol.nonterminal y.rule.input) }

/--
One step of the fixpoint iteration.
-/
def earleyFixpointBinStep (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (I : Set (EarleyItem T N)) : Set (EarleyItem T N) :=
  I ∪ scanFixpoint I w k ∪ completeFixpoint I k ∪ predictFixpoint G I k

/--
Fixpoint Iteration of a single bin.
-/
def earleyFixpointBin (G : ContextFreeGrammarList T N) (w : List T) (k : Nat)
    (I : Set (EarleyItem T N)) : Set (EarleyItem T N) :=
  Limit.limit (earleyFixpointBinStep G w k) I

/--
Set-based computation up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
def earleyFixpointBins (G : ContextFreeGrammarList T N) (w : List T) (k : Nat) :
    Set (EarleyItem T N) :=
  match k with
  | 0 => earleyFixpointBin G w 0 (initFixpoint G)
  | n+1 => earleyFixpointBin G w (n+1) (earleyFixpointBins G w n)

/--
Set-based/fixpoint iteration based computation of the EarleySet.
-/
def earleyFixpoint (G : ContextFreeGrammarList T N) (w : List T) : Set (EarleyItem T N) :=
  earleyFixpointBins G w w.length

end Fixpoint
end Earley
