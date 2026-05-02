module
public import Mathlib.Computability.ContextFreeGrammar

namespace Earley
namespace EarleyRecognizer

/--
An EarleyItem represents one the possible states the derivation could be in
while parsing the word.

The rule and the position jointly pinpoint what can be accepted next in this state,
while the startItem and endItem point back to the input index where this rule derivation started from.

TODO: Im not sure what the endItem really does yet. Its not really part of the original algorithm idea

We've got sets of EarleyItems for every input position

Maybe missing:
- the rule has to be part of the grammar G: do I need to sync it up like that?

TODO: implement Repr by hand to see dotted notation (maybe use @?)
      (should have some sanity checks though, else I debug the wrong thing :D)
      or do I want ToString? I want that notation anywhere right?
TODO: everything public now since I want to unit test it. There should be a way around that
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
  Startindex for the word w, which this rule accepts
  -/
  startItem : Nat
  /--
  (Exclusive) Endindex for the word w, which this rule accepts
  -/
  endItem : Nat

-- TODO: I think these instances make sense?
instance {T N : Type} [BEq T] [BEq N] : BEq (Symbol T N) where
  beq := fun fst snd => match fst,snd with
  | Symbol.terminal t₁, Symbol.terminal t₂ => t₁ == t₂
  | Symbol.terminal _, Symbol.nonterminal _ => False
  | Symbol.nonterminal _, Symbol.terminal _ => False
  | Symbol.nonterminal t₁, Symbol.nonterminal t₂ => t₁ == t₂

instance {T N : Type} [BEq T] [BEq N] : BEq (ContextFreeRule T N) where
  beq := fun fst snd => fst.input == snd.input && fst.output == snd.output

-- TODO: I could derive this one if I wanted to restrict EarleyItems to BEq Types in general
instance {T N : Type} [BEq T] [BEq N] : BEq (EarleyItem T N) where
  beq := fun fst snd => fst.rule == snd.rule
    && fst.position == snd.position
    && fst.startItem == snd.startItem
    && fst.endItem == snd.endItem

/- TODO: I want Repr over ToString, so I can read the output in proof states right? -/
instance {T N : Type} [Repr T] [Repr N] : Repr (Symbol T N) where
  reprPrec sym _ := match sym with
    | Symbol.terminal t => reprStr t
    | Symbol.nonterminal nt => reprStr nt

instance {T N : Type} [Repr T] [Repr N] : Repr (ContextFreeRule T N) where
  reprPrec rule _ := s!"{reprStr rule.input} → {reprStr rule.output}"

instance {T N : Type} [Repr T] [Repr N] : Repr (EarleyItem T N) where
  reprPrec item _ :=
    have ⟨lhs,rhs⟩ := item.rule.output.splitAt item.position
    s!"{reprStr item.rule.input} → {reprStr lhs} @ {reprStr rhs} w/ ({item.startItem}, {item.endItem})"

/--
Returns the rhs of given rule split at some index `i`
- rule=(A → α β) and i=1 returns ([α], [β])
- rule=(A → α β) and i=2 returns ([α, β], [])
- rule=(A → α β) and i=3 returns ([α, β], [])
-/
@[inline]
public def splitRuleAt {T N : Type} (rule : ContextFreeRule T N) (i : Nat) :
    List (Symbol T N) × List (Symbol T N) :=
  rule.output.splitAt i

/--
Returns the next symbol of the production of the item if there is one
- A → ·α returns some α
- A → α· returns none
-/
@[inline]
public def nextSymbol {T N : Type} (item : EarleyItem T N) : Option (Symbol T N):=
  item.rule.output[item.position]?

/--
Returns whether the rule of the EarleyItem is completed,
concretely if the position/dot is at the end of the production rule
- A → α· returns true
- A → ·α returns false
-/
@[inline]
public def isComplete {T N : Type} (item : EarleyItem T N) : Bool :=
  item.position == item.rule.output.length

/--
An item is finished w.r.t. a certain grammar G and the input word w, if
- the lhs of the rule is the startsymbol of G
- the item is complete
- the entire word has been recognized
-/
@[inline]
public def isFinished {T : Type} (G : ContextFreeGrammar T) [BEq G.NT]
    (item : EarleyItem T G.NT) (w : String) : Bool :=
  item.rule.input == G.initial
  && isComplete item
  && item.startItem == 0
  && item.endItem == w.length + 1
  -- TODO: this could very well be off by one

/--
An item is well-formed, if
- the rule belongs to given grammar G
- the position is within the length of the rhs
- the start is not bigger than the end
- the end is not bigger than the length of the input w
-/
public def isWellFormed {T : Type} [BEq T]
    (G : ContextFreeGrammar T) [BEq G.NT]
    (item : EarleyItem T G.NT) (w : String) : Prop :=
  G.rules.toList.contains item.rule
  ∧ item.position <= item.rule.output.length
  ∧ item.startItem <= item.endItem
  ∧ item.endItem <= w.length

/--
tail recursive helper
-/
public def reconizeAux : Bool := sorry

/--
Checks whether the input w is in the language defined by the grammar.
Process:
- Generate the Earley Items for the full input
- Check if there is a finished Item in the Set
-/
public def earleyRecognize {N T : Type} (w : Symbol T N) (G : ContextFreeGrammar T) : Bool := sorry


end EarleyRecognizer
end Earley
