import Mathlib.Computability.ContextFreeGrammar
import Earley.Earley
import Earley.EarleyRecognizer

namespace Recognizer
open EarleyRecognizer

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
deriving BEq, Repr

def exRule1 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a]

def exRule2 : ContextFreeRule T N where
  input := N.S
  output := [Symbol.terminal T.a, Symbol.nonterminal N.S]

def G : ContextFreeGrammarList T := {
  NT := N,
  initial := N.S,
  rules := [exRule1, exRule2],
  nodup := by simp [exRule1, exRule2]
}

/- Simple Unit Tests -/
-- TODO: I don't understand why
instance : BEq G.NT where
  beq fst snd := match fst,snd with
    | N.S, N.S => true

def exW1 : List T := [T.a]
def exW2 : List T := [T.a, T.a, T.a]
def exW3 : List T := [T.a, T.a]

-- {S -> aS | a}
--#eval! (recognizeTest G exW1)[1]
--#eval! recognizeList G []
--#eval! recognizeList G exW1
--#eval! recognizeList G exW2

--#eval! earleyBinsList G exW1 2
--#eval! earleyBinsList G exW1 1
--#eval! earleyBinsList G exW1 0

end Recognizer
