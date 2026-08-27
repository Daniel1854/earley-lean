/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Basic

/-!
This module represents the Earley parsing algorithm in a way which lends itself nicely to proofs.
The main definition is an inductively built set of the typing judgements from Earley.
It consists of EarleyItems, which represent one the possible states a derivation could be in
while parsing the word. Alternatively you can think of an EarleyItem as a partial parse.

The general idea of the algorithm is to built a set of EarleyItems for every input position,
and check for the final input position whether there is an item which parsed the full input
from the initial nonterminal.

The implementation follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Model

/--
An EarleyItem got four fields:
- a rule of the grammar
- a position within that rule
- the start- and endindex for the slice of the word, which this item handles

The `rule` and the `position` jointly define, which transitions can happen next.
The `startIdx` keeps track of where this item originated from.
The `endIdx` exists to keep track of the current index of the word.
-/
public structure EarleyItem (T N : Type) where
  /-- The rule of the item. -/
  rule : ContextFreeRule T N
  /-- The position within the rule. -/
  position : Nat
  /-- Startindex for a word, which this item recognizes. -/
  startIdx : Nat
  /-- (Exclusive) Endindex for a word, which this item recognizes. -/
  endIdx : Nat
deriving BEq, Hashable, ReflBEq, LawfulBEq, Repr

variable {T N : Type} [BEq N]

/--
Returns if a list of symbols include only terminals of given grammar.
-/
@[grind]
public def isWord (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) : Prop :=
  List.isEmpty (w.filter (fun s => match s with
    | Symbol.terminal _ => false
    | Symbol.nonterminal _ => true
  ))

/--
Returns the next symbol of the production of the item if there is one
- A → • α returns some α
- A → α • returns none
-/
@[inline, grind]
public def EarleyItem.nextSymbol (item : EarleyItem T N) : Option (Symbol T N) :=
  item.rule.output[item.position]?

/--
Returns the rhs of the rule of the item up to the dot.
- A → • β   returns []
- A → α • β returns [α]
-/
@[inline, grind]
public def EarleyItem.alphaItem (item : EarleyItem T N) : List (Symbol T N) :=
  item.rule.output.take item.position

/--
Returns the rhs of the item after the dot.
- A → α •   returns []
- A → α • β returns [β]
-/
@[inline, grind]
public def EarleyItem.betaItem (item : EarleyItem T N) : List (Symbol T N) :=
  item.rule.output.drop item.position

/--
Returns whether the rule of the EarleyItem is completed.
- A → α • returns true
- A → • α returns false
-/
@[inline, grind]
public def EarleyItem.isComplete (item : EarleyItem T N) : Bool :=
  item.position == item.rule.output.length

/--
An item is finished w.r.t. a certain initial symbol and the input word w, if
- the lhs of the rule is that initial symbol
- the item is complete
- the entire word has been recognized

Note: we use an arbitrary bound instead of attaching the word here since there is `w` as
      `List T | List (Symbol T N) | Array T` and a Nat is easier for now.
-/
@[inline, grind]
public def EarleyItem.isFinished (initial : N) (wlen : Nat) (item : EarleyItem T N) : Bool :=
  item.rule.input == initial
  && isComplete item
  && item.startIdx == 0
  && item.endIdx == wlen

/--
An item is well-formed, if
- the rule belongs to given ruleset
- the position is within the length of the rhs
- the start is not bigger than the end
- the end is not bigger than a bound. In practice the bound is the length of the input `w`,
  but since there is `w` as `List T | List (Symbol T N) | Array T` and a Nat is easier for now.
-/
@[grind]
public def EarleyItem.isWellFormed {R : Type} (rules : R) [Membership (ContextFreeRule T N) R]
    (wlen : Nat) (item : EarleyItem T N) : Prop :=
  item.rule ∈ rules
  ∧ item.position ≤ item.rule.output.length
  ∧ item.startIdx ≤ item.endIdx
  ∧ item.endIdx ≤ wlen

/--
Returns a new item with the position incremented by one and a new endIdx.
-/
@[inline, grind]
def EarleyItem.incItem (item : EarleyItem T N) (endIdx : Nat) : EarleyItem T N :=
  { item with position := item.position+1, endIdx := endIdx }

open EarleyItem

/--
This the inductive definition of the Earley Set.
Its purpose is only to prove correctness for the general judgement/ideas.
-/
@[grind cases]
public inductive EarleySet (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) :
    Set (EarleyItem T G.NT) where
  /--
  Every rule with the LHS matching the initial NT introduces an EarleyItem at the starting position.
  -/
  | init (rule : ContextFreeRule T G.NT) (hmem : rule ∈ G.rules) (hstart : rule.input = G.initial) :
      EarleySet G w ⟨rule,0,0,0⟩
  /--
  Every EarleyItem part of the set, where the next symbol matches the next input symbol,
  introduces an EarleyItem parsing that extra symbol.
  -/
  | scan {x : EarleyItem T G.NT} {rule : ContextFreeRule T G.NT} {pos i j : Nat}
      {a : Symbol T G.NT} (hx : x = ⟨rule,pos,i,j⟩) (hmem : x ∈ EarleySet G w)
      (hbounds : j < w.length) (hw : w[j] = a) (hnext : nextSymbol x = some a) :
      EarleySet G w ⟨rule,pos+1,i,j+1⟩
  /--
  Every EarleyItem part of set, where the next symbol matches the NT of another rule,
  introduces an EarleyItem where that rule gets followed through.
  -/
  | predict {x : EarleyItem T G.NT} {rule1 rule2 : ContextFreeRule T G.NT} {pos i j : Nat}
      (hx : x = ⟨rule1,pos,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hmemr2 : rule2 ∈ G.rules) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) :
      EarleySet G w ⟨rule2,0,j,j⟩
  /-
  Every completed EarleyItem part of the set introduces EarleyItems for where
  the rule could have originated from.
  -/
  | complete {x y : EarleyItem T G.NT} {rule1 rule2 : ContextFreeRule T G.NT}
      {posx posy i j k : Nat}
      (hx : x = ⟨rule1,posx,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hy : y = ⟨rule2,posy,j,k⟩) (hmemy : y ∈ EarleySet G w)
      (hcomp : isComplete y) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) :
      EarleySet G w ⟨rule1,posx+1,i,k⟩

end Model
end Earley
