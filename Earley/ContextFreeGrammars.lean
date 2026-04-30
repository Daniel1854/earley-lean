module
public import Mathlib.Computability.ContextFreeGrammar

/-!
This module defines everything required to parse a context-free grammar.
Basicly a wrapper around the `ContextFreeGrammar` definition within Mathlib,
but also includes a metaprogram to parse a String of EBNF into such a structure directly.
It doesn't handle epsilon rules.

Simple EBNF.
Usage         | Notation
--------------+----------------
definition	  | ::=
concatenation	| ,
termination	  | ;\n
alternation	  | |
terminals     | '<x>'

We cannot handle epsilon rules, so more syntactic sugar seems to not be worthwhile (yet)
Maybe add Regex + and * when we can handle epsilon rules?
optional	    | [ ... ]  (none or once)
repetition	  | { ... }  (none or more)
+             | at least once
*             | none or more

TODO: Requires some metaprogram to dynamicly create the inductive types of T and NT?
How to even state this as a one-pass? The return type doesnt exist before it would be called
I would very much like to directly return the list of that type as well,
but this doesnt seem possible?
inductive types are some syntactic sugar right? Not sure how to add that type in a metaprogram
⟨T,NT⟩ ← collectTypes
addDecl T ?
addDecl NT ?
parseCFG T NT s

def parseCFG (T NT : Type) (s : String) : ContextFreeGrammar T :=
  sorry

-/

namespace Earley
namespace ContextFreeGrammars

#check ContextFreeGrammar
#check Language
#check Language.IsContextFree
#check Symbol
#check ContextFreeRule
-- These are all about Prop so you can reason whether something multisteps to another thing,
-- so I need my own `step` version
#check ContextFreeGrammar.Produces  -- s -> u
#check ContextFreeGrammar.Derives   -- s ->^* u
#check ContextFreeGrammar.Generates -- S ->^* u
-- A little unclear on how this fits into the rest. Not sure if I can use it for something
-- (besides proofs)
#check ContextFreeRule.Rewrites
#check ContextFreeGrammar.mem_language_iff

inductive NT where
  | A : NT
  | B : NT
  | C : NT
  | D : NT
  | S : NT

inductive T where
  | a : T
  | b : T
  | c : T
  | d : T
  | s : T

-- this has the most important things.
-- A metaprogram could check the type of A if its NT or T and match accordingly
-- but how to handle if there are multiple terms?
notation (priority := high) E "::=" A ";" => ContextFreeRule.mk E [Symbol.terminal A]
#check [NT.S ::= T.a;, NT.S ::= T.a;]

-- how to coerce the string into the inductive type
-- how to coerce 'a' S into [T.a, NT.S]
def parseLine (s : String) : ContextFreeRule T NT:=
  sorry

--  G = ({S, a}, {a}, {S -> aS | a}, S)
-- TODO: this splitting style is ugly.
-- I dont think I will write up grammars that take tons of space,
-- but maybe think/research if I want to do it monadicly
-- TODO: startsymbol as a parameter?
def parseCFG (s : String) : Option (ContextFreeGrammar T) :=
  let lines := s.split (fun x => x == ';')
  let rules : Finset (ContextFreeRule T NT) :=
  {
    val := [NT.S ::= T.a;]
      --{ input := Ex1NT.S, output := [Symbol.terminal Ex1T.a] },
      --{ input := Ex1NT.S, output := [Symbol.nonterminal Ex1NT.S, Symbol.terminal Ex1T.a]}
    ,
    nodup := by simp
  }
  some { NT := NT, initial := NT.S, rules := rules }

def String.toNT : String → Option NT
  | "S" => some NT.S
  | _ => none

instance : CoeDep String "S" NT where
  coe := NT.S

def ex2NT : NT := "S"

def ex2CFG : String := "S ::= aS | a;"
def ex2CFG' : String := "\
S ::= aS;
S ::= a;"
def ex2CFG'' : String := "S ::= 'a'S | 'a'"

end ContextFreeGrammars
end Earley

