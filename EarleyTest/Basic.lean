import Mathlib.Computability.ContextFreeGrammar
import Earley.EarleyRecognizer

/-
This suite tests the basic functionality around EarleyItems

It tests the general mathlib API and basic usage of the functions for the example Grammar G
  G = ({S, a}, {a}, {S -> aS | a}, S) with L(G) = a⁺

TODO: write Tests for Repr
-/

/- Simple Usage Examples for Mathlib Types -/
inductive NT where
| S : NT
deriving Repr

inductive T where
| a : T
deriving Repr

def exRule1 : ContextFreeRule T NT where
  input := NT.S
  output := [Symbol.terminal T.a]

def exRule2 : ContextFreeRule T NT where
  input := NT.S
  output := [Symbol.terminal T.a, Symbol.nonterminal NT.S]

/--
info: NT.S → [T.a, NT.S]
-/
#guard_msgs in
#eval exRule2

set_option trace.Meta.synthInstance true in
#eval exRule2.output

def exRules : Finset (ContextFreeRule T NT) where
  val := { exRule1, exRule2 }
  nodup := by simp [exRule1, exRule2]

-- TODO: understand the design decision to not have NT as a parameter
-- (or atleast implicit from the `initial` field!)
def G : ContextFreeGrammar T :=
  { NT := NT, initial := NT.S, rules := exRules }

/-
Example theorems that the grammar can generate a certain word.

TODO: Im overlooking some good lemmas right? This shouldnt need that much unfolding.
Maybe the idea would be some mem_ lemmas?
Or people dont think this is a noteworthy thing to prove.
-/
theorem exProduces : G.Produces [Symbol.nonterminal NT.S] [Symbol.terminal T.a] := by
  unfold G
  unfold ContextFreeGrammar.Produces
  simp [exRules]
  apply Or.inl
  apply ContextFreeRule.Rewrites.head

theorem exGenerates (h : G.Produces [Symbol.nonterminal NT.S] [Symbol.terminal T.a]) : G.Generates [Symbol.terminal T.a] := by
  unfold ContextFreeGrammar.Generates
  unfold ContextFreeGrammar.Derives
  apply @Relation.ReflTransGen.tail (b:= [Symbol.nonterminal NT.S])
  . unfold G
    apply Relation.ReflTransGen.refl
  . exact h

-- Reminder:
-- Sets in Mathlib are Prop. It is only about reasoning if an item is a part of that set
def exLanguage : Language T := G.language

/--
info: {w | G.Generates (List.map Symbol.terminal w)} : Set (List T)
-/
#guard_msgs in
#check { w : List T | G.Generates (w.map Symbol.terminal) }

/- Simple Unit Tests -/

open Earley.EarleyRecognizer

/--
info: ([], [T.a, NT.S])
-/
#guard_msgs in
#eval splitRuleAt exRule2 0

/--
info: ([T.a], [NT.S])
-/
#guard_msgs in
#eval splitRuleAt exRule2 1

/--
info: ([T.a, NT.S], [])
-/
#guard_msgs in
#eval splitRuleAt exRule2 2

/--
info: ([T.a, NT.S], [])
-/
#guard_msgs in
#eval splitRuleAt exRule2 3

def exItem1 : EarleyItem T NT where
  rule := exRule2
  position := 0
  startItem := 0
  endItem := 0

def exItem2 : EarleyItem T NT :=
  { exItem1 with position := 1 }

def exItem3 : EarleyItem T NT :=
  { exItem1 with position := 2, startItem := 1 }

/--
info: NT.S → T.a @ NT.S w/ (0, 0)
-/
#guard_msgs in
#eval exItem2

/--
info: some T.a
-/
#guard_msgs in
#eval nextSymbol exItem1

/--
info: some NT.S
-/
#guard_msgs in
#eval nextSymbol exItem2

/--
info: none
-/
#guard_msgs in
#eval nextSymbol exItem3

def exW : String := "aaa"

#check isComplete

#check isFinished

#check isWellFormed
