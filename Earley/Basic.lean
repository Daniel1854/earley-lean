module
public import Mathlib.Computability.ContextFreeGrammar
public import Lean.LibrarySuggestions.Default

deriving instance BEq for Symbol
deriving instance ReflBEq for Symbol
deriving instance LawfulBEq for Symbol
deriving instance BEq for ContextFreeRule
deriving instance ReflBEq for ContextFreeRule
deriving instance LawfulBEq for ContextFreeRule

-- TODO: These types don't require anything else and should be included everywhere.
--       At least a namespace would be useful, maybe it should be a separate file regardless.

/--
Variant of `ContextFreeGrammar` that uses a List internally to store the rules.
Context-free grammar that generates words over the alphabet `T` (a type of terminals).
-/
public structure ContextFreeGrammarList (T N : Type) where
  /-- Initial nonterminal. -/
  initial : N
  /-- Rewrite rules. -/
  rules : List (ContextFreeRule T N)
  /-- `rules` contains no duplicates -/
  nodup : List.Nodup rules

/--
A ContextFreeGrammar is equal to a ContextFreeGrammarList iff
their initial symbols and their rules match.
-/
@[grind]
public def ContextFreeGrammarEqContextFreeGrammarList {T : Type}
  (G : ContextFreeGrammar T) (Gₗ : ContextFreeGrammarList T G.NT) : Prop :=
  G.initial = Gₗ.initial ∧ G.rules.toList = Gₗ.rules

public abbrev CFGEqCFGₗ {T : Type} (G : ContextFreeGrammar T) (Gₗ : ContextFreeGrammarList T G.NT) :
    Prop :=
  ContextFreeGrammarEqContextFreeGrammarList G Gₗ

/--
A CFG is equal to a CFGₗ iff their initial symbols and their rules match.
-/
@[simp, grind =]
public theorem eq_of_CFGEqCFGₗ {T : Type} (G : ContextFreeGrammar T)
    (Gₗ : ContextFreeGrammarList T G.NT) : CFGEqCFGₗ G Gₗ ↔
    G.initial = Gₗ.initial ∧ G.rules.toList = Gₗ.rules := by
  grind
