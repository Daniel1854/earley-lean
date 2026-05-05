module
public import Earley.Earley

@[expose] public section

/-!
This module houses the correctness proofs for
- Earley Typing Judgements / EarleySet
- Earley Recognizer
- Earley Parser
-/

namespace Earley
namespace Invariants

section EarleySet

variable {T N : Type} [BEq T] [BEq N] [Repr T] [Repr N]

/--
The EarleySet only has a finite number of element.
-/
theorem finiteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Finite (EarleySet G w) := by
  sorry

/--
Any EarleyItem within an EarleySet is well-formed.
-/
theorem wfEarley (G : ContextFreeGrammar T) [BEq G.NT] (x : EarleyItem T G.NT)
    (w : List (Symbol T G.NT)) (hmem : x ∈ EarleySet G w) : isWellFormed G x w := by
  sorry

/--
The soundness criteria for the EarleySet:
Given a finished item for a word within the set,
the grammar has to be able to generate that word.
-/
theorem soundnessEarley {G : ContextFreeGrammar T} [BEq G.NT] {x : EarleyItem T G.NT}
    {w : List (Symbol T G.NT)} (hmem : x ∈ EarleySet G w) (hfin : isFinished G x w) :
    G.Generates w := by
  sorry

/--
The completeness criteria for the EarleySet:
Given a word the grammar can generate,
there has to be a finished item within the corresponding EarleySet.
-/
theorem completenessEarley {G : ContextFreeGrammar T} [BEq G.NT] {w : List (Symbol T G.NT)}
    (hgen : G.Generates w) : ∃ x ∈ EarleySet G w, isFinished G x w:= by
  sorry

/--
The correctness criteria for the EarleySet.

A word can be generated from the grammar
iff
there exists a finished item within the corresponding EarleySet.
-/
theorem correctnessEarley {G : ContextFreeGrammar T} [BEq G.NT] {w : List (Symbol T G.NT)} :
    G.Generates w ↔ ∃ x ∈ EarleySet G w, isFinished G x w := by
  constructor
  · intro hgen
    apply completenessEarley hgen
  · intro hex
    rcases hex with ⟨hw,h⟩
    apply soundnessEarley h.left h.right

end EarleySet

end Invariants
end Earley
