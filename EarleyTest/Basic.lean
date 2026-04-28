import Mathlib.Computability.ContextFreeGrammar

example (n : Nat) : n = n := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (n m : Nat) : n = m := by simp

/-
Testing out mathlib API with the example Grammar G
  G = ({S, a}, {a}, {S -> aS | a}, S)
  L(G) = a⁺
-/
inductive Ex1NT where
| S : Ex1NT
deriving Repr

inductive Ex1T where
| a : Ex1T
deriving Repr

/--
info: ContextFreeRule Ex1T Ex1NT : Type
-/
#guard_msgs in
#check ContextFreeRule Ex1T Ex1NT

def ex1Rules : Finset (ContextFreeRule Ex1T Ex1NT) :=
  {
    val := {
      { input := Ex1NT.S, output := [Symbol.terminal Ex1T.a] },
      { input := Ex1NT.S, output := [Symbol.nonterminal Ex1NT.S, Symbol.terminal Ex1T.a]}
    },
    nodup := by simp
  }

def ex1CFG : ContextFreeGrammar Ex1T :=
  -- Why can't NT be derived from initial?
  { NT := Ex1NT, initial := Ex1NT.S, rules := ex1Rules }

open ContextFreeGrammar
open ContextFreeRule

-- Im overlooking some good lemmas right? This shouldnt need that much unfolding.
-- Maybe there are some mem_ lemmas? Or people dont think this is a noteworthy thing to prove
theorem ex1Produces : ex1CFG.Produces [Symbol.nonterminal Ex1NT.S] [Symbol.terminal Ex1T.a] := by
  simp [ex1CFG]
  simp [Produces]
  simp [ex1Rules]
  apply Or.inl
  apply Rewrites.head

theorem ex1Generates (h : ex1CFG.Produces [Symbol.nonterminal Ex1NT.S] [Symbol.terminal Ex1T.a]) : ex1CFG.Generates [Symbol.terminal Ex1T.a] := by
  simp [Generates]
  simp [Derives]
  apply @Relation.ReflTransGen.tail (b:= [Symbol.nonterminal Ex1NT.S])
  . simp [ex1CFG]
    apply Relation.ReflTransGen.refl
  . exact h

-- Sets in Mathlib are Prop, and thus you cannot get its item,
-- but you can reason if its part of that set
def ex1Language : Language Ex1T := ex1CFG.language
/--
info: {w | ex1CFG.Generates (List.map Symbol.terminal w)} : Set (List Ex1T)
-/
#guard_msgs in
#check { w : List Ex1T | ex1CFG.Generates (w.map Symbol.terminal) }
