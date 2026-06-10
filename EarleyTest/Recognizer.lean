import Earley.Model
import Earley.Recognizer
import Earley.Fixpoint
import Earley.Parser

import Mathlib.Computability.ContextFreeGrammar

/-!
This suite tests the basic functionality of the Recognizer and Parser.

TODO: Unclear if these Repr instances are worthwhile for anything besides these tests.
      Should they be ToString?
-/

namespace Recognizer
open Earley.Recognizer
open Earley.Fixpoint
open Earley.Parser

variable {α β : Type} [Repr α] [Repr β] [ToString α] [ToString β]

def saveTree (t : Option (Tree α β)) (name : String) : IO Unit :=
  match t with
  | some t => IO.FS.writeFile name (toGraphviz t)
  | none => pure ()

instance : Repr (Symbol α β) where
 reprPrec sym _ := match sym with
   | Symbol.terminal t => reprStr t
   | Symbol.nonterminal nt => reprStr nt

instance : Repr ReductionPointer where
  reprPrec p _ := s!"({p.endIdxA},{p.i},{p.j})"

instance : Repr Pointer where
 reprPrec sym _ := match sym with
   | Pointer.null => "null"
   | Pointer.predecessor i => s!"pre {i}"
   | Pointer.reduction ps => s!"red {reprStr ps}"

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
deriving BEq

instance : Repr N where
 reprPrec sym _ := match sym with
   | N.S => "N.S"

instance : ToString N where
 toString sym := match sym with
   | N.S => "N.S"

inductive T where
| a : T
| b : T
deriving BEq

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
#eval! (earleyList G exW3)[1]
/--
info: []
-/
#guard_msgs in
#eval! (earleyList G exW3)[2]
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
info: false
-/
#guard_msgs in
#eval! recognizeList G exW3

/--
info: some (Earley.Parser.Tree.node
  (Symbol.nonterminal N.S)
  [Earley.Parser.Tree.leaf (Symbol.terminal T.a),
   Earley.Parser.Tree.node (Symbol.nonterminal N.S) [Earley.Parser.Tree.leaf (Symbol.terminal T.a)]])
-/
#guard_msgs in
#eval! (parse G [T.a, T.a])

-- #eval! saveTree (parse G [T.a, T.a]) "Examples/tree1.gv"

end BasicExample

/-
Less simple example:
Sum     -> Sum     + Product | Product
Product -> Product * Factor  | Factor
Factor  -> '(' Sum ')' | 0 | 1 | 2
-/
namespace LessBasicExample

inductive N where
| Sum : N
| Product : N
| Factor : N
deriving BEq

instance : Repr N where
 reprPrec sym _ := match sym with
   | N.Sum => "N.Sum"
   | N.Product => "N.Product"
   | N.Factor => "N.Factor"

instance : ToString N where
 toString sym := match sym with
   | N.Sum => "N.Sum"
   | N.Product => "N.Product"
   | N.Factor => "N.Factor"

inductive T where
| Plus : T
| Mul : T
| Open : T
| Close : T
| Zero : T
| One : T
| Two : T
deriving BEq

instance : Repr T where
 reprPrec sym _ := match sym with
  | T.Plus => "T.Plus"
  | T.Mul => "T.Mul"
  | T.Open => "T.Open"
  | T.Close => "T.Close"
  | T.Zero => "T.Zero"
  | T.One => "T.One"
  | T.Two => "T.Two"

instance : ToString T where
 toString sym := match sym with
  | T.Plus => "T.Plus"
  | T.Mul => "T.Mul"
  | T.Open => "T.Open"
  | T.Close => "T.Close"
  | T.Zero => "T.Zero"
  | T.One => "T.One"
  | T.Two => "T.Two"

def exRule1 : ContextFreeRule T N where
  input := N.Sum
  output := [Symbol.nonterminal N.Sum, Symbol.terminal T.Plus, Symbol.nonterminal N.Product]
def exRule2 : ContextFreeRule T N where
  input := N.Sum
  output := [Symbol.nonterminal N.Product]
def exRule3 : ContextFreeRule T N where
  input := N.Product
  output := [Symbol.nonterminal N.Product, Symbol.terminal T.Mul, Symbol.nonterminal N.Factor]
def exRule4 : ContextFreeRule T N where
  input := N.Product
  output := [Symbol.nonterminal N.Factor]
def exRule5 : ContextFreeRule T N where
  input := N.Factor
  output := [Symbol.terminal T.Open, Symbol.nonterminal N.Sum, Symbol.terminal T.Close]
def exRule6 : ContextFreeRule T N where
  input := N.Factor
  output := [Symbol.terminal T.Zero]
def exRule7 : ContextFreeRule T N where
  input := N.Factor
  output := [Symbol.terminal T.One]
def exRule8 : ContextFreeRule T N where
  input := N.Factor
  output := [Symbol.terminal T.Two]
def G : ContextFreeGrammarList T N := {
  initial := N.Sum,
  rules := [exRule1, exRule2, exRule3, exRule4, exRule5, exRule6, exRule7, exRule8],
  nodup := by simp [exRule1, exRule2, exRule3, exRule4, exRule5, exRule6, exRule7, exRule8]
}

def exW1 : List T := [T.Zero]
def exW2 : List T := [T.Zero, T.Plus, T.One]
def exW3 : List T := [T.Zero, T.Mul, T.One, T.Plus, T.One]
def exW4 : List T := [T.Open, T.One, T.Plus, T.Zero, T.Close, T.Mul, T.Two]
def exW5 : List T := [T.Mul, T.Plus, T.One]

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
info: true
-/
#guard_msgs in
#eval! recognizeList G exW4
/--
info: false
-/
#guard_msgs in
#eval! recognizeList G exW5

/--
info: some (Earley.Parser.Tree.node
  (Symbol.nonterminal N.Sum)
  [Earley.Parser.Tree.node
     (Symbol.nonterminal N.Product)
     [Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.Zero)]]])
-/
#guard_msgs in
#eval! (parse G exW1)
/--
info: some (Earley.Parser.Tree.node
  (Symbol.nonterminal N.Sum)
  [Earley.Parser.Tree.node
     (Symbol.nonterminal N.Sum)
     [Earley.Parser.Tree.node
        (Symbol.nonterminal N.Product)
        [Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.Zero)]]],
   Earley.Parser.Tree.leaf (Symbol.terminal T.Plus),
   Earley.Parser.Tree.node
     (Symbol.nonterminal N.Product)
     [Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.One)]]])
-/
#guard_msgs in
#eval! (parse G exW2)
/--
info: some (Earley.Parser.Tree.node
  (Symbol.nonterminal N.Sum)
  [Earley.Parser.Tree.node
     (Symbol.nonterminal N.Sum)
     [Earley.Parser.Tree.node
        (Symbol.nonterminal N.Product)
        [Earley.Parser.Tree.node
           (Symbol.nonterminal N.Product)
           [Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.Zero)]],
         Earley.Parser.Tree.leaf (Symbol.terminal T.Mul),
         Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.One)]]],
   Earley.Parser.Tree.leaf (Symbol.terminal T.Plus),
   Earley.Parser.Tree.node
     (Symbol.nonterminal N.Product)
     [Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.One)]]])
-/
#guard_msgs in
#eval! (parse G exW3)
/--
info: some (Earley.Parser.Tree.node
  (Symbol.nonterminal N.Sum)
  [Earley.Parser.Tree.node
     (Symbol.nonterminal N.Product)
     [Earley.Parser.Tree.node
        (Symbol.nonterminal N.Product)
        [Earley.Parser.Tree.node
           (Symbol.nonterminal N.Factor)
           [Earley.Parser.Tree.leaf (Symbol.terminal T.Open),
            Earley.Parser.Tree.node
              (Symbol.nonterminal N.Sum)
              [Earley.Parser.Tree.node
                 (Symbol.nonterminal N.Sum)
                 [Earley.Parser.Tree.node
                    (Symbol.nonterminal N.Product)
                    [Earley.Parser.Tree.node
                       (Symbol.nonterminal N.Factor)
                       [Earley.Parser.Tree.leaf (Symbol.terminal T.One)]]],
               Earley.Parser.Tree.leaf (Symbol.terminal T.Plus),
               Earley.Parser.Tree.node
                 (Symbol.nonterminal N.Product)
                 [Earley.Parser.Tree.node
                    (Symbol.nonterminal N.Factor)
                    [Earley.Parser.Tree.leaf (Symbol.terminal T.Zero)]]],
            Earley.Parser.Tree.leaf (Symbol.terminal T.Close)]],
      Earley.Parser.Tree.leaf (Symbol.terminal T.Mul),
      Earley.Parser.Tree.node (Symbol.nonterminal N.Factor) [Earley.Parser.Tree.leaf (Symbol.terminal T.Two)]]])
-/
#guard_msgs in
#eval! (parse G exW4)
/-- info: none -/
#guard_msgs in
#eval! (parse G exW5)

--#eval! saveTree (parse G exW4) "Examples/tree2.gv"

end LessBasicExample

end Recognizer
