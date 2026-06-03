import Earley.Model
import Earley.Recognizer
import Earley.Fixpoint

import Mathlib.Computability.ContextFreeGrammar

namespace Recognizer
open Earley.Recognizer
open Earley.Fixpoint

/-
This suite tests the basic functionality of the Recognizer

It plays with the general mathlib API and basic usage of the functions for the example Grammar G
  G = ({S, a}, {a}, {S -> aS | a}, S) with L(G) = a⁺

TODO: test basic functionality with decently complicated grammar
-/

/- Simple Usage Examples for Mathlib Types -/
inductive N where
| S : N
deriving BEq, Repr

inductive T where
| a : T
| b : T
deriving BEq, Repr

def exRule1 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a]

def exRule2 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a, Symbol.nonterminal N.S]

def G : ContextFreeGrammarList T N := {
  initial := N.S,
  rules := [exRule1, exRule2],
  nodup := by simp [exRule1, exRule2]
}

def exW1 : List T := [T.a]
def exW2 : List T := [T.a, T.a, T.a]
def exW3 : List T := [T.a, T.a]
def exW4 : List T := [T.a, T.b]

instance : Repr T where
 reprPrec sym _ := match sym with
   | T.a => "T.a"
   | T.b => "T.b"

instance : Repr N where
 reprPrec sym _ := match sym with
   | N.S => "N.S"

instance : Repr (Symbol T N) where
 reprPrec sym _ := match sym with
   | Symbol.terminal t => reprStr t
   | Symbol.nonterminal nt => reprStr nt

instance : Repr (ReductionPointer) where
  reprPrec p _ := s!"({p.endItemA},{p.i},{p.j})"

instance : Repr (Pointer) where
 reprPrec sym _ := match sym with
   | Pointer.null => "null"
   | Pointer.predecessor i => s!"pre {i}"
   | Pointer.reduction ps => s!"red {reprStr ps}"

instance {T N : Type} [Repr T] [Repr N] : Repr (ContextFreeRule T N) where
  reprPrec rule _ := s!"{reprStr rule.input} → {reprStr rule.output}"

instance : Repr (Earley.Model.EarleyItem T N) where
  reprPrec item _ :=
    have ⟨lhs,rhs⟩ := item.rule.output.splitAt item.position
    have input := reprStr item.rule.input
    s!"({input} → {reprStr lhs} @ {reprStr rhs}, {item.startItem}, {item.endItem})"

instance : Repr (Earley.Recognizer.BinItem T N) where
  reprPrec item _ :=
    s!"({reprStr item.item}, {reprStr item.pointer})"

/-- info: [((N.S → [] @ [T.a], 0, 0), null), ((N.S → [] @ [T.a, N.S], 0, 0), null)] -/
#guard_msgs in
#eval! (earleyList G exW1)[0]
/--
info: [((N.S → [T.a] @ [], 0, 1), pre 0),
 ((N.S → [T.a] @ [N.S], 0, 1), pre 1),
 ((N.S → [] @ [T.a], 1, 1), null),
 ((N.S → [] @ [T.a, N.S], 1, 1), null)]
-/
#guard_msgs in
#eval! (earleyList G exW1)[1]
/--
info: [((N.S → [T.a] @ [], 1, 2), pre 2),
 ((N.S → [T.a] @ [N.S], 1, 2), pre 3),
 ((N.S → [T.a, N.S] @ [], 0, 2), red [(1,1,0)]),
 ((N.S → [] @ [T.a], 2, 2), null),
 ((N.S → [] @ [T.a, N.S], 2, 2), null)]
-/
#guard_msgs in
#eval! (earleyList G exW2)[2]
/--
info: [((N.S → [T.a] @ [], 2, 3), pre 3),
 ((N.S → [T.a] @ [N.S], 2, 3), pre 4),
 ((N.S → [T.a, N.S] @ [], 1, 3), red [(2,1,0)]),
 ((N.S → [] @ [T.a], 3, 3), null),
 ((N.S → [] @ [T.a, N.S], 3, 3), null),
 ((N.S → [T.a, N.S] @ [], 0, 3), red [(1,1,2)])]
-/
#guard_msgs in
#eval! (earleyList G exW2)[3]
/--
info: [((N.S → [T.a] @ [], 0, 1), pre 0),
 ((N.S → [T.a] @ [N.S], 0, 1), pre 1),
 ((N.S → [] @ [T.a], 1, 1), null),
 ((N.S → [] @ [T.a, N.S], 1, 1), null)]
-/
#guard_msgs in
#eval! (earleyList G exW4)[1]
/--
info: []
-/
#guard_msgs in
#eval! (earleyList G exW4)[2]
/--
info: []
-/
#guard_msgs in
#eval! (earleyList G [T.b, T.b])[1]

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
info: true
-/
#guard_msgs in
#eval! recognizeList G exW3
/--
info: false
-/
#guard_msgs in
#eval! recognizeList G exW4

end Recognizer
