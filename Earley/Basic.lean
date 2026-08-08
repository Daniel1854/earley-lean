module
public import Mathlib.Computability.ContextFreeGrammar
public import Lean.LibrarySuggestions.Default

/-!
This module houses basic types and instances, that should be included everywhere.
-/

deriving instance BEq for Symbol
deriving instance ReflBEq for Symbol
deriving instance LawfulBEq for Symbol
deriving instance Hashable for Symbol
deriving instance BEq for ContextFreeRule
deriving instance ReflBEq for ContextFreeRule
deriving instance LawfulBEq for ContextFreeRule
deriving instance Hashable for ContextFreeRule

namespace Earley

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

public abbrev mapT {T N : Type} (w : Array T) : List (Symbol T N) :=
  (w.toList).map Symbol.terminal

@[simp, grind =]
public theorem map_of_mapT {T N : Type} (w : Array T) :
    (mapT w : List (Symbol T N)) = (w.toList).map Symbol.terminal := by
  simp [mapT]

@[inline, grind]
public def Vector.modify {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (f : α → α) :
    Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

@[grind =]
public theorem Vector.getElem_modify {α : Type} {n : Nat} {xs : Vector α n} {i j : Nat} (f : α → α)
    (hi : i < n) : (Vector.modify xs j f)[i] = if j = i then f xs[i] else xs[i] := by
  simp only [modify, Vector.getElem_mk]
  grind

public theorem Std.HashMap.getD_of_map {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] {f : β → β}
    {k : α} (m : Std.HashMap α (List β)) :
    (m.map (fun _ xs => xs.map f)).getD k [] = (m.getD k []).map f := by
  match h : m[k]? with
  | none => grind [Std.HashMap.getD_eq_fallback_of_contains_eq_false]
  | some val => grind [Std.HashMap.getElem?_eq_some_getD]

end Earley
