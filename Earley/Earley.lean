module
public import Mathlib.Computability.ContextFreeGrammar
@[expose] public section

/-!
This module represents the general Earley parsing algorithm in a way
which lends itself nicely to proofs.
Concretely the main definition is an inductively built set of the typing judgements from Earley.
The set consists of EarleyItems, which represent one the possible states the derivation could be in
while parsing the word or more concretely it's a state of a partial parse.

The general idea of the algorithm is to built sets of EarleyItems for every input position,
and check at the end whether there is an item which showcases
that the whole input got parsed from the initial Nonterminal.
-/

namespace Earley

/--
An inductive definition of `List.extract`, which lends itself easier to proofs.
The first parameter is the List, which is to be sliced.
The second is the start index, and the third is the (exclusive) end index

Examples from the List.extract docstring:
* [0, 1, 2, 3, 4, 5].slice 1 2 = [1]
* [0, 1, 2, 3, 4, 5].slice 2 2 = []
* [0, 1, 2, 3, 4, 5].slice 2 4 = [2, 3]
-/
public def slice {α : Type} : List α → Nat → Nat → List α
  | [], _, _ => []
  | _::_, _, 0 => []
  | x::xs, 0, (m+1) => x :: slice xs 0 m
  | _::xs, (n+1), (m+1) => slice xs n m

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

-- TODO: I want Repr over ToString, so I can read the output in proof states right?
variable {T N : Type} [BEq N] [Repr T] [Repr N]

instance : Repr (Symbol T N) where
  reprPrec sym _ := match sym with
    | Symbol.terminal t => reprStr t
    | Symbol.nonterminal nt => reprStr nt

instance : Repr (ContextFreeRule T N) where
  reprPrec rule _ := s!"{reprStr rule.input} → {reprStr rule.output}"

instance : Repr (EarleyItem T N) where
  reprPrec item _ :=
    have ⟨lhs,rhs⟩ := item.rule.output.splitAt item.position
    have input := reprStr item.rule.input
    s!"{input} → {reprStr lhs} @ {reprStr rhs} w/ ({item.startItem}, {item.endItem})"

/--
Returns the rhs of given rule split at some index `i`
- rule=(A → α β) and i=1 returns ([], [β])
- rule=(A → α β) and i=2 returns ([α, β], [])
- rule=(A → α β) and i=3 returns ([α, β], [])
-/
@[inline]
public def splitRuleAt (rule : ContextFreeRule T N) (i : Nat) :
    List (Symbol T N) × List (Symbol T N) :=
  rule.output.splitAt i

/--
Returns the next symbol of the production of the item if there is one
- A → •α returns some α
- A → α• returns none
-/
@[inline]
public def nextSymbol (item : EarleyItem T N) : Option (Symbol T N) :=
  item.rule.output[item.position]?

/--
Returns the rhs of the rule of the item up to the dot.
- A → • β   returns []
- A → α • β returns [α]
-/
@[inline]
public def alphaItem (item : EarleyItem T N) : List (Symbol T N) :=
  item.rule.output.take item.position

/--
Returns the rhs of the item after the dot.
- A → α •   returns []
- A → α • β returns [β]
-/
@[inline]
public def betaItem (item : EarleyItem T N) : List (Symbol T N) :=
  item.rule.output.drop item.position

/--
Returns whether the rule of the EarleyItem is completed,
concretely if the position/dot is at the end of the production rule
- A → α• returns true
- A → •α returns false

TODO: rau thinks it should be >=, but really no reason for?
-/
@[inline]
public def isComplete (item : EarleyItem T N) : Bool :=
  item.position == item.rule.output.length

/--
An item is finished w.r.t. a certain grammar G and the input word w, if
- the lhs of the rule is the startsymbol of G
- the item is complete
- the entire word has been recognized
-/
@[inline]
public def isFinished (G : ContextFreeGrammar T) [BEq (G.NT)] (w : List (Symbol T G.NT))
    (item : EarleyItem T G.NT) : Bool :=
  item.rule.input == G.initial
  && isComplete item
  && item.startItem == 0
  && item.endItem == w.length

/--
This the inductive definition of the Earley Set.
Its purpose is only to prove correctness for the general judgement/ideas.
-/
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
      (hbounds : j < w.length) (hw : w[j] = a)
      (hnext : nextSymbol x = some a)
      : EarleySet G w ⟨rule,pos+1,i,j+1⟩
  /--
  Every EarleyItem part of set, where the next symbol matches the NT of another rule,
  introduces an EarleyItem where that rule gets followed through.
  -/
  | predict (x : EarleyItem T G.NT) (rule1 rule2 : ContextFreeRule T G.NT) (pos i j : Nat)
      (a : Symbol T G.NT) (hx : x = ⟨rule1,pos,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hmemr2 : rule2 ∈ G.rules) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input))
      (hbounds : j < w.length) (hw : w[j] = a)
      : EarleySet G w ⟨rule2,0,j,j⟩
  /-
  Every completed EarleyItem part of the set introduces EarleyItems for where
  the rule could have originated from.
  -/
  | complete (x y : EarleyItem T G.NT) (rule1 rule2 : ContextFreeRule T G.NT)
      (posx posy i j k : Nat)
      (hx : x = ⟨rule1,posx,i,j⟩) (hmemx : x ∈ EarleySet G w)
      (hy : y = ⟨rule2,posy,j,k⟩) (hmemy : y ∈ EarleySet G w)
      (hcomp : isComplete y) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input))
      : EarleySet G w ⟨rule1,posx+1,i,k⟩

end Earley
