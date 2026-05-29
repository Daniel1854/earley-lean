module
public import Earley.Basic
@[expose] public section

/-!
This module represents the general Earley parsing algorithm in a way
which lends itself nicely to proofs.
Concretely the main definition is an inductively built set of the typing judgements from Earley.
The set consists of EarleyItems, which represent one the possible states the derivation could be in
while parsing the word or more concretely it's a state of a partial parse.

The general idea of the algorithm is to built sets of EarleyItems for every input position,
and check at the end whether there is an item which showcases
that the whole input got parsed from the initial nonterminal.

The implementation follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

namespace Earley
namespace Model

/--
An EarleyItem got four fields:
- a rule of the grammar
- a position within that rule
- the start- and endindex of the word which the rule handles

The rule and the position jointly pinpoint what can be accepted next in this state,
while the startItem enables pointing back to the input index
where this rule derivation started from.
The endIndex exists since this inductive definition is not a List of Sets,
where each item of the List represents the EarleySet for a specific input position.
Thus we need to keep track of it another way.
-/
public structure EarleyItem (T N : Type) where
  /--
  The rule the item is representing
  -/
  rule : ContextFreeRule T N
  /--
  The position within the `rule`
  -/
  position : Nat
  /--
  Startindex for the word w which this rule recognizes
  -/
  startItem : Nat
  /--
  (Exclusive) Endindex for the word w which this rule recognizes
  -/
  endItem : Nat
deriving BEq, Repr

variable {T N : Type}

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
- A → •α returns some α
- A → α• returns none
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
Returns whether the rule of the EarleyItem is completed,
concretely if the position/dot is at the end of the production rule
- A → α• returns true
- A → •α returns false

TODO: rau thinks it should be >=, but really no reason for?
-/
@[inline, grind]
public def EarleyItem.isComplete (item : EarleyItem T N) : Bool :=
  item.position == item.rule.output.length

/--
An item is finished w.r.t. a certain grammar G and the input word w, if
- the lhs of the rule is the startsymbol of G
- the item is complete
- the entire word has been recognized
-/
@[inline, grind]
public def EarleyItem.isFinished (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (item : EarleyItem T G.NT) : Bool :=
  item.rule.input == G.initial
  && isComplete item
  && item.startItem == 0
  && item.endItem == w.length

/--
An item is well-formed, if
- the rule belongs to given grammar G
- the position is within the length of the rhs
- the start is not bigger than the end
- the end is not bigger than the length of the input w
-/
@[grind]
public def EarleyItem.isWellFormed (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (item : EarleyItem T G.NT) : Prop :=
  item.rule ∈ G.rules
  ∧ item.position <= item.rule.output.length
  ∧ item.startItem <= item.endItem
  ∧ item.endItem <= w.length

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
  | scan (x : EarleyItem T G.NT) (rule : ContextFreeRule T G.NT) (pos i j : Nat)
      (a : Symbol T G.NT) (hx : x = ⟨rule,pos,i,j⟩) (hmem : x ∈ EarleySet G w)
      (hbounds : j < w.length) (hw : w[j] = a) (hnext : nextSymbol x = some a) :
      EarleySet G w ⟨rule,pos+1,i,j+1⟩
  /--
  Every EarleyItem part of set, where the next symbol matches the NT of another rule,
  introduces an EarleyItem where that rule gets followed through.
  -/
  | predict (x : EarleyItem T G.NT) (rule1 rule2 : ContextFreeRule T G.NT) (pos i j : Nat)
      (hx : x = ⟨rule1,pos,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hmemr2 : rule2 ∈ G.rules) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) :
      EarleySet G w ⟨rule2,0,j,j⟩
  /-
  Every completed EarleyItem part of the set introduces EarleyItems for where
  the rule could have originated from.
  -/
  | complete (x y : EarleyItem T G.NT) (rule1 rule2 : ContextFreeRule T G.NT)
      (posx posy i j k : Nat)
      (hx : x = ⟨rule1,posx,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hy : y = ⟨rule2,posy,j,k⟩) (hmemy : y ∈ EarleySet G w)
      (hcomp : isComplete y) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) :
      EarleySet G w ⟨rule1,posx+1,i,k⟩

end Model
end Earley
