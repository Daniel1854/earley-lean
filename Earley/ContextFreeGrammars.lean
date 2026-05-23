/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Mathlib.Computability.ContextFreeGrammar
--import Lean

/-!
This module defines everything required to parse a context-free grammar.
Basicly a wrapper around the `ContextFreeGrammar` definition within Mathlib,
but also includes a metaprogram to parse a String of BNF into such a structure directly.

Simple BNF.
Using "::=" for definition. Nonterminal symbols as is, terminal ones surrounded by "'".
"|" for adding a second rhs to a lhs rule. ";\n" to denote the ending of a rule.
ε for the empty rule.
Whitespace between symbols? A ::= ε 'a' will probably not be well defined :D

Example:
A ::= 'a' A | 'a';
B ::= A 'b' S | 'a' | ε ;

Plan:
A metaprogram creating the inductive types of T and NT as the first pass,
then notation should suffice for actually parsing it into a ContextFreeGrammar struct?
I dont think you can do this through one pass, but the grammar itself shouldnt be too long anyway.

TODO: Its fine to return something of a new type as long as you return that type as well?
TODO: startsymbol as a parameter?
TODO: how to coerce the string into these types?

@ref: Algebra.adjoin for macro stuff

addDecl (.axiomDecl {
  name := `Exists, levelParams := [`u],
  type := mkForall `α .implicit sortu $ ← mkArrow (← mkArrow (mkBVar 0) prop) prop,
  isUnsafe := false
})
-/

namespace Earley
namespace ContextFreeGrammars

open Lean Lean.Expr Lean.Meta

public inductive NT where
  | A : NT
  | B : NT
  | C : NT
  | D : NT
  | S : NT
deriving Repr

public inductive T where
  | a : T
  | b : T
  | c : T
  | d : T
  | s : T
deriving Repr

/--
Metaprogram to parse from a BNF-style String all the occuring terminals and non-terminals,
and create an inductive type for each of them.

TODO: this splitting style is ugly.
I dont think I will write up grammars that take tons of space,
but maybe think/research if I want to do it more proper.

TODO: alternative to addDecl
let cmd ← `(command|
    inductive $name : Type where
    $[| $ctorNames:ident : $ctorTypes:term]*
-/
def createSymbols (s : String) (ntName : String) (tName : String) : CoreM Unit :=
  --let lines := s.split (fun x => x == ';')
  --let inducts := #[]
  -- inductDecl (lparams : List Name) (nparams : Nat)
  -- (types : List InductiveType) (isUnsafe : Bool) : Declaration
  -- why is types a list of inductivetype?
  addDecl <| .inductDecl [] 0
  [⟨`Earley.ContextFreeGrammars.NonTerminals, .sort 1,
  [⟨`Earley.ContextFreeGrammars.NonTerminals.S,
    .const `Earley.ContextFreeGrammars.NonTerminals.S []⟩]⟩] false

#check InductiveType
--#eval createSymbols "" "" ""

-- A metaprogram could check the type of A if its NT or T and match accordingly
-- but how to handle if there are multiple terms?
def parseIntoCFG (T : Type) (s : String) : Option (ContextFreeGrammar T) :=
  sorry

notation (priority := high) E "::=" A ";" => ContextFreeRule.mk E [Symbol.terminal A]

def rule := NT.S ::= T.a;
--#eval rule.input
--#eval rule.output

-- how to coerce "'a' S" into [T.a, NT.S]
--def parseLine (s : String) : ContextFreeRule T NT:=
--  sorry
def String.toNT : String → Option NT
  | "S" => some NT.S
  | _ => none

instance : CoeDep String "S" NT where
  coe := NT.S

def ex2CFG : String := "S ::= 'a' S | a;"
-- createTypes ex2CFG -> G = ⟨NT,NT.S, {NT.S → [T.a, NT.S], NT.S → [T.a]}⟩

def ex2CFG' : String := "\
S ::= 'a' S;
S ::= 'a';"
def ex2CFG'' : String := "S ::= 'a' S | 'a'"

end ContextFreeGrammars
end Earley

