module
public import Mathlib.Computability.ContextFreeGrammar

namespace Earley
namespace EarleyRecognizer

/--
An EarleyItem

We've got sets of EarleyItems for every input position

Maybe missing:
- the rule has to be part of the grammar G: do I need to sync it up like that?

I want to be able to see the dotted (maybe use @?) notation in my repr for an EarleyItem
prob should have some sanity check tests for that though

TODO: write Tests for these functions
-/
structure EarleyItem (T N: Type) where
  /--
  The rule the item describes
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

/--
Returns the rhs of given rule split at some index `i`
- rule=(A → α β) and i=1 returns ([α], [β])
- rule=(A → α β) and i=2 returns ([], [α, β])
-/
@[inline]
def splitRuleAt {T N : Type} (rule : ContextFreeRule T N) (i : Nat) :
    List (Symbol T N) × List (Symbol T N) :=
  rule.output.splitAt i

/--
Returns whether the rule of the EarleyItem is completed,
concretely if the position/dot is at the end of the production rule
- A → α· returns true
- A → ·α returns false
-/
@[inline]
def isComplete {T N : Type} (item : EarleyItem T N) : Bool :=
  item.position == item.rule.output.length

/--
Returns the next symbol of the production of the item if there is one
- A → ·α returns some α
- A → α· returns none
-/
def nextSymbol {T N : Type} (item : EarleyItem T N) : Option (Symbol T N):=
  item.rule.output[item.position]?

/--
An item is finished w.r.t. a certain grammar G and the input word w, if
- the lhs of the rule is the startsymbol of G
- the item is complete
- the entire word has been recognized
-/
def isFinished {T : Type} (G : ContextFreeGrammar T) [BEq G.NT] (w : String) (item : EarleyItem T G.NT) : Bool :=
  item.rule.input == G.initial &&
  isComplete item && item.startItem == 0 && item.endItem == w.length + 1
  -- TODO: this could very well be off by one

-- the item dot must be within the length of the item’s right-hand side,
-- the item start does not exceed the item end,
-- and finally, the item end must be at most the length of the input ω.
/--
An item is well-formed, if
- the rule belongs to given grammar G
- the position is within the length of the rhs
-/
def wfItem {T N : Type} (item : EarleyItem T N) : Prop :=
  sorry

/--
tail recursive helper
-/
def reconizeAux : Bool := sorry

/--
Checks whether the input w is in the language defined by the grammar.
Process:
- Generate the Earley Items for the full input
- Check if there is a finished Item in the Set
-/
def earleyRecognize {N T : Type} (w : Symbol T N) (cfg : ContextFreeGrammar T) : Bool := sorry


end EarleyRecognizer
end Earley
