import Mathlib.Computability.ContextFreeGrammar

/-!
This module defines everything required to parse a context-free grammar.
In particular this has:
- the tuple with some invariant?
- the macro to parse an EBNF String into grammar

Contextfree grammar, instance of it contains:
- production rules: List Rule (lhs, rhs) with lhs=a single symbol & rhs= List Symbols
- start symbol
need to check that the grammar is actually contextfree, but I guess that happens automaticly with the chosen type?

List Token
Token = Terminal | NonTerminal
NonTerminal = Union(lhs) union StartSymbol
Word: a sentence containing only terminal letters
Empty Symbol empty list?
Derivation G α D β : you can derive beta from alpha with the Grammar G through derivation D with D being a List of production rules with indices


Macro: uppercase as nonterminals, lowercase as terminals
What is the point of having Terminals and Non-Terminals as a concrete Type
-/

namespace Earley
namespace ContextFreeGrammars

#check ContextFreeGrammar
#check Language --
#check Language.IsContextFree
#check Symbol
#check ContextFreeRule
#check ContextFreeRule.Rewrites
#check ContextFreeGrammar.Produces  -- s -> u
#check ContextFreeGrammar.Derives   -- s ->^* u
#check ContextFreeGrammar.Generates -- S ->^* u

def example_grammar : ContextFreeGrammar String :=
  {
    NT := sorry
    initial := sorry
    rules := sorry
  }

inductive ExampleAlphabet where
  | a : ExampleAlphabet
  | b : ExampleAlphabet

def example_language : Language ExampleAlphabet := sorry

-- words of a language should only consist of terminals, how does that check happen?
#check ContextFreeGrammar.mem_language_iff

end ContextFreeGrammars
end Earley

