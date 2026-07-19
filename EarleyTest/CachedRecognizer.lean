/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
import Earley.Model
import Earley.CachedRecognizer

/-!
This suite tests the basic functionality of the Recognizer and Parser.

TODO: Unclear if these Repr instances are worthwhile for anything besides these tests.
      Should they be ToString?
-/

namespace CachedRecognizer
open Earley.CachedRecognizer

variable {α β : Type} [Repr α] [Repr β] [ToString α] [ToString β]

instance : Repr (Symbol α β) where
 reprPrec sym _ := match sym with
   | Symbol.terminal t => reprStr t
   | Symbol.nonterminal nt => reprStr nt

instance : Repr (ContextFreeRule α β) where
  reprPrec rule _ := s!"{reprStr rule.input} → {reprStr rule.output}"

instance : Repr (Earley.Model.EarleyItem α β) where
  reprPrec item _ :=
    have ⟨lhs,rhs⟩ := item.rule.output.splitAt item.position
    have input := reprStr item.rule.input
    s!"({input} → {reprStr lhs} @ {reprStr rhs}, {item.startIdx}, {item.endIdx})"

instance : Repr (Earley.Recognizer.BinItem α β) where
  reprPrec item _ :=
    s!"({reprStr item.item}, {reprStr item.pointer})"

/- Simplest Example: S → a | aS -/
namespace BasicExample

inductive N where
| S : N
deriving BEq, Hashable, ReflBEq, LawfulBEq

instance : Repr N where
 reprPrec sym _ := match sym with
   | N.S => "N.S"

instance : ToString N where
 toString sym := match sym with
   | N.S => "N.S"

inductive T where
| a : T
| b : T
deriving BEq, Hashable, ReflBEq, LawfulBEq

instance : Repr T where
 reprPrec sym _ := match sym with
   | T.a => "T.a"
   | T.b => "T.b"

instance : ToString T where
 toString sym := match sym with
   | T.a => "T.a"
   | T.b => "T.b"

def exRule1 : ContextFreeRule T N := ⟨N.S, [Symbol.terminal T.a]⟩
def exRule2 : ContextFreeRule T N := ⟨N.S, [Symbol.terminal T.a, Symbol.nonterminal N.S]⟩

def G : ContextFreeGrammarList T N := {
  initial := N.S,
  rules := [exRule1, exRule2],
  nodup := by simp [exRule1, exRule2]
}

def exW1 : List T := [T.a]
def exW2 : List T := [T.a, T.a, T.a]
def exW3 : List T := [T.a, T.b]

/-- info: #[(N.S → [] @ [T.a], 0, 0), (N.S → [] @ [T.a, N.S], 0, 0)] -/
#guard_msgs in
#eval! (earleyList G exW1).bins[0].raw
/--
info: #[(N.S → [T.a] @ [], 0, 1), (N.S → [T.a] @ [N.S], 0, 1), (N.S → [] @ [T.a], 1, 1), (N.S → [] @ [T.a, N.S], 1, 1)]
-/
#guard_msgs in
#eval! (earleyList G exW1).bins[1].raw
/--
info: #[(N.S → [T.a] @ [], 1, 2), (N.S → [T.a] @ [N.S], 1, 2), (N.S → [T.a, N.S] @ [], 0, 2), (N.S → [] @ [T.a], 2, 2),
  (N.S → [] @ [T.a, N.S], 2, 2)]
-/
#guard_msgs in
#eval! (earleyList G exW2).bins[2].raw
/--
info: #[(N.S → [T.a] @ [], 2, 3), (N.S → [T.a] @ [N.S], 2, 3), (N.S → [T.a, N.S] @ [], 1, 3), (N.S → [] @ [T.a], 3, 3),
  (N.S → [] @ [T.a, N.S], 3, 3), (N.S → [T.a, N.S] @ [], 0, 3)]
-/
#guard_msgs in
#eval! (earleyList G exW2).bins[3].raw
/--
info: #[(N.S → [T.a] @ [], 0, 1), (N.S → [T.a] @ [N.S], 0, 1), (N.S → [] @ [T.a], 1, 1), (N.S → [] @ [T.a, N.S], 1, 1)]
-/
#guard_msgs in
#eval! (earleyList G exW3).bins[1].raw
/-- info: #[] -/
#guard_msgs in
#eval! (earleyList G exW3).bins[2].raw
/-- info: #[] -/
#guard_msgs in
#eval! (earleyList G [T.b, T.b]).bins[1].raw

/--
info: false
-/
#guard_msgs in
#eval! recognizeList G []
/--
info: true
-/
#guard_msgs in
#eval! recognizeList G exW1
/--
info: true
-/
#guard_msgs in
#eval! recognizeList G exW2
/--
info: false
-/
#guard_msgs in
#eval! recognizeList G exW3

end BasicExample
end CachedRecognizer
