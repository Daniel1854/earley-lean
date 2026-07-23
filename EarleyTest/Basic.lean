/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
import Earley.Model
import Earley.Recognizer

/-!
This suite tests the basic functionality around EarleyItems

It plays with the general mathlib API and basic usage of the functions for the example Grammar G
  G = ({S, a}, {a}, {S -> aS | a}, S) with L(G) = a⁺
-/

namespace Basic

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

def exRule3 : ContextFreeRule T N where
  input := N.S
  output := []

def exRules : Finset (ContextFreeRule T N) where
  val := { exRule1, exRule2, exRule3 }
  nodup := by simp [exRule1, exRule2, exRule3]

def G : ContextFreeGrammar T :=
  { NT := N, initial := N.S, rules := exRules }

/-
Example theorems that the grammar can generate a certain word.
-/
theorem exProduces : G.Produces [Symbol.nonterminal N.S] [Symbol.terminal T.a] := by
  unfold G
  unfold ContextFreeGrammar.Produces
  unfold exRules
  use exRule1
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.mem_cons, Finset.mem_mk,
    Multiset.mem_singleton, true_or, true_and]
  apply ContextFreeRule.Rewrites.head

theorem exProducesEps : G.Produces [Symbol.nonterminal N.S] [] := by
  unfold G
  unfold ContextFreeGrammar.Produces
  unfold exRules
  use exRule3
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.mem_cons, Finset.mem_mk,
    Multiset.mem_singleton, or_true, true_and]
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

/- Simple Unit Tests -/
open Earley
open Model
open Model.EarleyItem

def exItem1 : EarleyItem T N where
  rule := exRule2
  position := 0
  startIdx := 0
  endIdx := 0

def exItem2 : EarleyItem T N :=
  { exItem1 with position := 1, startIdx := 1, endIdx:= 2 }

def exItem3 : EarleyItem T N :=
  { exItem1 with position := 2, startIdx := 1 , endIdx:= 0 }

def exItem4 : EarleyItem T N :=
  { exItem1 with position := 3, startIdx := 1 , endIdx:= 2 }

def exItem5 : EarleyItem T N where
  rule := exRule1
  position := 1
  startIdx := 0
  endIdx := 1

theorem next1 : nextSymbol exItem1 = some (Symbol.terminal T.a) := rfl
theorem next2 : nextSymbol exItem2 = some (Symbol.nonterminal N.S) := rfl
theorem next3 : nextSymbol exItem3 = none := rfl

theorem complete1 : isComplete exItem1 = false := rfl
theorem complete2 : isComplete exItem2 = false := rfl
theorem complete3 : isComplete exItem3 = true := rfl
theorem complete4 : isComplete exItem4 = false := rfl

-- TODO: I don't understand why. This is derived, but somehow I need it explicit since it's a field?
instance : BEq G.NT where
  beq fst snd := match fst,snd with
    | N.S, N.S => true

def exW1 : List (Symbol T N) := [Symbol.terminal T.a]
def exW2 : List (Symbol T N) := [Symbol.terminal T.a, Symbol.terminal T.a, Symbol.terminal T.a]
def exW3 : List (Symbol T N) := [Symbol.nonterminal N.S, Symbol.terminal T.a, Symbol.terminal T.a]
theorem finished1 : isFinished G.initial exW1.length exItem1 = false := rfl
theorem finished2 : isFinished G.initial exW1.length exItem2 = false := rfl
theorem finished3 : isFinished G.initial exW1.length exItem3 = false := rfl
theorem finished4 : isFinished G.initial exW1.length exItem4 = false := rfl
theorem finished5 : isFinished G.initial exW1.length exItem5 = true := rfl

theorem wf1 : isWellFormed G.rules exW1.length exItem1 := by
  rw [isWellFormed, exItem1]
  unfold G
  unfold exRules
  simp

theorem wf2 : ¬isWellFormed G.rules exW1.length exItem2 := by
  rw [isWellFormed, exItem2, exW1]
  simp [List.length]

theorem wf3 : ¬isWellFormed G.rules exW2.length exItem3 := by
  rw [isWellFormed, exItem3]
  simp

theorem wf4 : ¬isWellFormed G.rules exW2.length exItem4 := by
  rw [isWellFormed, exItem4, exItem1, exW2, exRule2]
  simp [List.length]

theorem wf5 : isWellFormed G.rules exW2.length exItem5 := by
  rw [isWellFormed, exItem5, exW2]
  unfold G
  unfold exRules
  simp [List.length, exRule1]

theorem isWord1 : isWord G exW1 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW1]

theorem isWord2 : isWord G exW2 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW2]

theorem isWord3 : ¬isWord G exW3 := by
  simp [isWord, G, exRules, exRule1, exRule2, exW3]

end Basic
