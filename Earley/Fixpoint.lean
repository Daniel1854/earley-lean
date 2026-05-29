module
public import Earley.Model
@[expose] public section

/-!
This module represents a fixpoint implementation of the Earley algorithm.
It's a stepping stone to refine from the inductive definition to the fully functional one.

A bit unclear where exactly this helps! This seems to just strip some syntactic sugar away.
But maybe there is some relation to the bins that helps!
-/

namespace Earley
namespace Fixpoint

open Model
open EarleyItem

/--
Variant of `ContextFreeGrammar` that uses a List internally to store the rules.
Context-free grammar that generates words over the alphabet `T` (a type of terminals).
-/
structure ContextFreeGrammarList (T : Type) where
  /-- Type of nonterminals. -/
  NT : Type
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : List (ContextFreeRule T NT)
  /-- `rules` contains no duplicates -/
  nodup : List.Nodup rules

variable {T : Type} {N : Type}

/--
Returns if the grammar contains a rule with an empty rhs.
-/
def isEpsilonFree (G : ContextFreeGrammarList T) : Prop :=
  ∀ r ∈ G.rules, !r.output.isEmpty

/--
Returns the subset of `I` where endItem is equal to `k`.
Corresponds to the i-th bin in the list-based algorithm.
-/
def bin (I : Set (EarleyItem T N)) (k : Nat) : Set (EarleyItem T N) :=
  { x ∈ I | x.endItem = k }

/--
Returns the subset of `I` where prevSymbol is a terminal.

Denotes the subset of I that forms the k-th base of a bin,
meaning the subset of I containing only items of the form A → αa • β, i, j,
where a is a terminal symbol preceding the dot.
If k is zero, base ω I 0 consists of all initial items S G → •α, 0, 0
-> TODO: I dont see how that would be the case with this definition huh
TODO: Rau uses a slightly different version:
  prevSymbol x = Some (w[k-1]!)
I dont think I can make that work, but I am also not sure what exactly ! denotes in Isabelle
-/
def base (I : Set (EarleyItem T N)) (w : List (Symbol T N)) (k : Nat) : Set (EarleyItem T N) :=
  { x ∈ I | x.endItem = k ∧ k > 0 ∧ prevSymbol x = w[k-1]?}

/--
Set-based implementation of the .init operation.
Returns a set filled with all possible .init states.

TODO: Set (EarleyItems) - how does it differ from the Model?
It simply describes a set of items and not how to construct them inductively I suppose
but through sheer application of operations? The technical difference seems quite low
-/
def initFixpoint (G : ContextFreeGrammarList T) [BEq G.NT] : Set (EarleyItem T G.NT) :=
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
def predictFixpoint (G : ContextFreeGrammarList T) (I : Set (EarleyItem T G.NT)) (k : Nat) :
    Set (EarleyItem T G.NT) :=
  { ⟨r,pos,i,j⟩ | ∀ x, pos = 0 ∧ i = 0 ∧ j = 0 ∧
    (r ∈ G.rules) ∧ x ∈ bin I k ∧ nextSymbol x = some (Symbol.nonterminal r.input) }

/--
Set-based implementation of the .complete operation.
-/
def completeFixpoint (I : Set (EarleyItem T N)) (k : Nat) :
    Set (EarleyItem T N) :=
  { z | ∀ x y : EarleyItem T N, z = incItem x k ∧ x ∈ bin I y.startItem ∧
    y ∈ bin I k ∧ isComplete y ∧ nextSymbol x = some (Symbol.nonterminal y.rule.input) }

/--
One step of the fixpoint iteration
-/
def earleyFixpointBinStep (G : ContextFreeGrammarList T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  I ∪ scanFixpoint I w k ∪ completeFixpoint I k ∪ predictFixpoint G I k

/--
Fixpoint Iteration of a single bin
-/
def earleyFixpointBin (G : ContextFreeGrammarList T) (w : List (Symbol T G.NT)) (k : Nat)
    (I : Set (EarleyItem T G.NT)) : Set (EarleyItem T G.NT) :=
  -- TODO: "limit"
  (earleyFixpointBinStep G w k) I

/--
TODO
Builds the stack
-/
def earleyFixpointBins (G : ContextFreeGrammarList T) [BEq G.NT] (w : List (Symbol T G.NT))
    (k : Nat) : Set (EarleyItem T G.NT) :=
  match k with
  | 0 => earleyFixpointBin G w 0 (initFixpoint G)
  | n+1 => earleyFixpointBin G w (n+1) (earleyFixpointBins G w n)

/--
Set-based/fixpoint iteration based computation of the EarleySet
-/
def earleyFixpoint (G : ContextFreeGrammarList T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Set (EarleyItem T G.NT) :=
  earleyFixpointBins G w w.length

end Fixpoint
end Earley
