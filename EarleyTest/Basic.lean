import Mathlib.Computability.ContextFreeGrammar
import Earley.Earley
import Earley.Invariants

/-
This suite tests the basic functionality around EarleyItems

It tests the general mathlib API and basic usage of the functions for the example Grammar G
  G = ({S, a}, {a}, {S -> aS | a}, S) with L(G) = a⁺
-/

/- Simple Usage Examples for Mathlib Types -/
inductive N where
| S : N
deriving BEq, Repr

inductive T where
| a : T
deriving BEq, Repr

def exRule1 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a]

def exRule2 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a, Symbol.nonterminal N.S]

/--
info: N.S → [T.a, N.S]
-/
#guard_msgs in
#eval exRule2

def exRules : Finset (ContextFreeRule T N) where
  val := { exRule1, exRule2 }
  nodup := by simp [exRule1, exRule2]

def G : ContextFreeGrammar T :=
  { NT := N, initial := N.S, rules := exRules }

/-
Example theorems that the grammar can generate a certain word.

TODO: Im overlooking some good lemmas right? This shouldnt need that much unfolding.
Maybe the idea would be some mem_ lemmas?
Or people dont think this is a noteworthy thing to prove.
-/
theorem exProduces : G.Produces [Symbol.nonterminal N.S] [Symbol.terminal T.a] := by
  unfold G
  unfold ContextFreeGrammar.Produces
  unfold exRules
  use exRule1
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.mem_cons, Finset.mem_mk,
    Multiset.mem_singleton, true_or, true_and]
  apply ContextFreeRule.Rewrites.head

theorem exGenerates (h : G.Produces [Symbol.nonterminal N.S] [Symbol.terminal T.a]) :
    G.Generates [Symbol.terminal T.a] := by
  unfold ContextFreeGrammar.Generates
  unfold ContextFreeGrammar.Derives
  apply @Relation.ReflTransGen.tail (b := [Symbol.nonterminal N.S])
  · unfold G
    apply Relation.ReflTransGen.refl
  · exact h

-- Reminder:
-- Sets in Mathlib are Prop. It is only about reasoning if an item is a part of that set
def exLanguage : Language T := G.language

/--
info: {w | G.Generates (List.map Symbol.terminal w)} : Set (List T)
-/
#guard_msgs in
#check { w : List T | G.Generates (w.map Symbol.terminal) }

/- Simple Unit Tests -/
open Earley

theorem split0 :
    splitRuleAt exRule2 0 = ⟨[], [Symbol.terminal T.a, Symbol.nonterminal N.S]⟩
  := rfl
theorem split1 :
    splitRuleAt exRule2 1 = ⟨[Symbol.terminal T.a], [Symbol.nonterminal N.S]⟩
  := rfl
theorem split2 :
    splitRuleAt exRule2 2 = ⟨[Symbol.terminal T.a, Symbol.nonterminal N.S], []⟩
  := rfl
theorem split3 :
    splitRuleAt exRule2 3 = ⟨[Symbol.terminal T.a, Symbol.nonterminal N.S], []⟩
  := rfl

def exItem1 : EarleyItem T N where
  rule := exRule2
  position := 0
  startItem := 0
  endItem := 0

def exItem2 : EarleyItem T N :=
  { exItem1 with position := 1, startItem := 1, endItem := 2 }

def exItem3 : EarleyItem T N :=
  { exItem1 with position := 2, startItem := 1 , endItem := 0 }

def exItem4 : EarleyItem T N :=
  { exItem1 with position := 3, startItem := 1 , endItem := 2 }

def exItem5 : EarleyItem T N where
  rule := exRule1
  position := 1
  startItem := 0
  endItem := 1

/--
info: N.S → [] @ [T.a, N.S] w/ (0, 0)
-/
#guard_msgs in
#eval exItem1

/--
info: N.S → [T.a] @ [N.S] w/ (1, 2)
-/
#guard_msgs in
#eval exItem2

/--
info: N.S → [T.a, N.S] @ [] w/ (1, 0)
-/
#guard_msgs in
#eval exItem3

/--
info: N.S → [T.a, N.S] @ [] w/ (1, 2)
-/
#guard_msgs in
#eval exItem4

theorem next1 : nextSymbol exItem1 = some (Symbol.terminal T.a) := rfl
theorem next2 : nextSymbol exItem2 = some (Symbol.nonterminal N.S) := rfl
theorem next3 : nextSymbol exItem3 = none := rfl

theorem complete1 : isComplete exItem1 = false := rfl
theorem complete2 : isComplete exItem2 = false := rfl
theorem complete3 : isComplete exItem3 = true := rfl
theorem complete4 : isComplete exItem4 = false := rfl

-- TODO: this is already derived, but I want to understand why this isnt enough
instance : BEq N where
  beq fst snd := match fst,snd with
    | N.S, N.S => true

-- TODO: I don't understand why
instance : BEq G.NT where
  beq fst snd := match fst,snd with
    | N.S, N.S => true

def exW1 : List (Symbol T N) := [Symbol.terminal T.a]
def exW2 : List (Symbol T N) := [Symbol.terminal T.a, Symbol.terminal T.a, Symbol.terminal T.a]
def exW3 : List (Symbol T N) := [Symbol.nonterminal N.S, Symbol.terminal T.a, Symbol.terminal T.a]
theorem finished1 : isFinished G exW1 exItem1 = false := rfl
theorem finished2 : isFinished G exW1 exItem2 = false := rfl
theorem finished3 : isFinished G exW1 exItem3 = false := rfl
theorem finished4 : isFinished G exW1 exItem4 = false := rfl
theorem finished5 : isFinished G exW1 exItem5 = true := rfl

open Invariants
-- These just wait for lemmas, which I will require anyway for the proofs right?
  -- [Finset.mem_toList]
theorem wf1 : isWellFormed G exW1 exItem1 := by
  rw [isWellFormed, exItem1]
  unfold G
  unfold exRules
  simp

theorem wf2 : ¬isWellFormed G exW1 exItem2 := by
  rw [isWellFormed, exItem2, exW1]
  simp [List.length]

theorem wf3 : ¬isWellFormed G exW2 exItem3 := by
  rw [isWellFormed, exItem3]
  simp

theorem wf4 : ¬isWellFormed G exW2 exItem4 := by
  rw [isWellFormed, exItem4, exItem1, exW2, exRule2]
  simp [List.length]

theorem wf5 : isWellFormed G exW2 exItem5 := by
  rw [isWellFormed, exItem5, exW2]
  unfold G
  unfold exRules
  simp [List.length, exRule1]

-- TODO: refer to some material in MIL with sets? I am a bit surprised how bad these are to handle
theorem ntsG : nonterminals G = { Symbol.nonterminal N.S } := by
  simp [nonterminals, G, exRules, exRule1, exRule2]
  grind

theorem isWord1 : isWord G exW1 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW1]

theorem isWord2 : isWord G exW2 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW2]

theorem isWord3 : ¬isWord G exW3 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW3]
