module
public import Earley.Earley
public import Earley.Slice
public import Earley.Derivation
@[expose] public section

/-!
TODO: maybe rename this file/see how it develops
This module houses the correctness proofs for the EarleySet and maybe more?
-/

namespace Earley
namespace Invariants

section EarleySet

variable {T : Type} {N : Type}

@[simp]
lemma alphaItem_of_zero (item : EarleyItem T N) (h : item.position = 0) :
    alphaItem item = [] := by
  simp [alphaItem, h]

@[simp]
lemma betaItem_of_zero (item : EarleyItem T N) (h : item.position = 0) :
    betaItem item = item.rule.output := by
  simp [betaItem, h]

@[simp]
lemma alphaItem_of_len (item : EarleyItem T N) (h : item.position = item.rule.output.length) :
    alphaItem item = item.rule.output := by
  simp [alphaItem, h]

@[simp]
lemma betaItem_of_len (item : EarleyItem T N) (h : item.position = item.rule.output.length) :
    betaItem item = [] := by
  simp [betaItem, h]

section WellFormed

/--
An item is well-formed, if
- the rule belongs to given grammar G
- the position is within the length of the rhs
- the start is not bigger than the end
- the end is not bigger than the length of the input w
-/
public def isWellFormed (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (item : EarleyItem T G.NT) : Prop :=
  item.rule ∈ G.rules
  ∧ item.position <= item.rule.output.length
  ∧ item.startItem <= item.endItem
  ∧ item.endItem <= w.length

/--
If there is a next symbol, then the position `pos+1` is still in bounds of the rhs of the rule.
-/
lemma bounds_of_nextSymbol_eq_some {G : ContextFreeGrammar T} {x : EarleyItem T G.NT}
    {a : Symbol T G.NT} (h : nextSymbol x = some a) : x.position + 1 ≤ x.rule.output.length := by
  rw [nextSymbol] at h
  have := of_getElem?_eq_some h
  omega

/--
Any EarleyItem within an EarleySet is well-formed.
TODO: maybe split these up like I did with `soundItemEarley`? only if I need them somewhere else
-/
public theorem wfEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (x : EarleyItem T G.NT) (hmem : x ∈ EarleySet G w) : isWellFormed G w x := by
  unfold isWellFormed
  induction hmem with
  | init rule hmem hstart => simp [hmem]
  | scan x rule pos i j a hx hmem hbounds hw hnext ih =>
    simp only
    have := bounds_of_nextSymbol_eq_some hnext
    simp only [hx] at ih this
    refine ⟨ih.left,this,by omega⟩
  | predict x rule1 rule2 pos i j a hx hmem hr2 hnext hbounds hw ih =>
    simp only
    simp only [hx] at ih
    refine ⟨hr2,by omega⟩
  | complete x y rule1 rule2 posx posy i j k hx hmemx hy hmemy hcomp hnext ihx ihy =>
    simp only
    have := bounds_of_nextSymbol_eq_some hnext
    simp only [hx] at ihx this
    simp only [hy] at ihy
    refine ⟨ihx.left,this, by omega⟩

end WellFormed

section Soundness
open ContextFreeRule
open ContextFreeGrammar

/--
An item (A → α • β, i, j) for a word w is sound, if
by starting the grammar at the input of the rule of the item (A)
you can derive the i'th up to but exluding the j'th symbol of the word
followed by the remaining beta.
-/
public def isSound (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (item : EarleyItem T G.NT) : Prop :=
  let parsedAlpha := slice w item.startItem item.endItem
  G.Derives [Symbol.nonterminal item.rule.input] <| parsedAlpha ++ betaItem item

/--
Any well-formed EarleyItem within an EarleySet, where the position is zero, is sound
This is the case for the .init and .predict constructor.
Since the new item `A → •α, j, j` is at the beginning of the rule and w_j/j = [],
we only need to show that A derives α, which is exactly the rule.
-/
public theorem soundItemPosZero (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {rule : ContextFreeRule T G.NT} {j : Nat} (hmem : rule ∈ G.rules) :
    isSound G w ⟨rule,0,j,j⟩ := by
  unfold isSound
  simp only
  apply Produces.single
  use rule
  simp [hmem, Rewrites.input_output]

/--
Any EarleyItem within an EarleySet produced through the .scan constructor is sound.
Given item `A → α • a β, i, j` we can derive `A → α a • β, i, j+1`:
To prove soundness of the new item, we need to show A deriving w_i/j+1 ++ β
from A deriving w_i/j ++ (a :: β).
Since we know that the next symbol is `a`, this is mostly reasoning with slice/drop.
-/
public theorem soundItemScan (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {x : EarleyItem T G.NT} {rule : ContextFreeRule T G.NT} {pos i j : Nat} {a : Symbol T G.NT}
    (hx : x = ⟨rule, pos, i, j⟩) (hmem : x ∈ EarleySet G w) (hbounds : j < w.length)
    (hw : w[j] = a) (hnext : nextSymbol x = some a) (hsound : isSound G w x) :
    isSound G w ⟨rule,pos+1,i,j+1⟩ := by
  simp only [isSound, betaItem]
  simp only [isSound, betaItem, hx] at hsound
  simp only [nextSymbol, hx] at hnext
  -- Split the expected parse into w_i/j ++ [a]
  have wfx := wfEarley G w x hmem
  simp [isWellFormed, hx] at wfx
  have := slice_succ_right w wfx.right.right.left hbounds
  simp only [this, hw]
  -- Use the trailing [a] to get rid of the off by one
  have := getElem_of_getElem? hnext
  rcases this with ⟨hbounds,hpos⟩
  have := @List.getElem_cons_drop _ rule.output pos hbounds
  rw [hpos] at this
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [this]
  exact hsound

/--
Any EarleyItem within an EarleySet produced through the .complete constructor is sound.
Given item x `A → α • B β` and item y `B → γ •`, we can derive the item `A → α B • β`
with approriate indices. This proof operates like the one for .scan, but we have to chain
two substrings together: the one for α and the one for γ.
-/
public theorem soundItemComplete (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {x y : EarleyItem T G.NT} {rule1 rule2 : ContextFreeRule T G.NT} {posx posy i j k : Nat}
    (hx : x = ⟨rule1, posx, i, j⟩) (hmemx : x ∈ EarleySet G w)
    (hy : y = ⟨rule2, posy, j, k⟩) (hmemy : y ∈ EarleySet G w)
    (hcomp : isComplete y) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input))
    (hsoundx : isSound G w x) (hsoundy : isSound G w y) :
    isSound G w ⟨rule1,posx+1,i,k⟩ := by
  simp only [isSound, betaItem]
  simp only [isSound, betaItem, hx, hy] at hsoundx hsoundy
  simp [isComplete, hy] at hcomp
  simp only [hcomp, List.drop_length, List.append_nil] at hsoundy
  -- Derive using the first rule
  apply Derives.trans hsoundx
  have wfx := wfEarley G w x hmemx
  have wfy := wfEarley G w y hmemy
  simp [isWellFormed, hx, hy] at wfx wfy
  have : slice w i j ++ slice w j k = slice w i k := by
    exact @slice_concat _ w i j k (by omega) (by omega)
  rw [← this]
  -- Remove matching Prefix
  rw [List.append_assoc]
  apply Derives.append_left _ (slice w i j)
  -- Pop out the non-terminal for rule2/y
  simp only [nextSymbol, hx] at hnext
  have := getElem_of_getElem? hnext
  rcases this with ⟨hbounds,hpos⟩
  have := @List.getElem_cons_drop _ rule1.output posx hbounds
  rw [← this]
  -- Remove matching Postfix
  rw [hpos]
  rw [← List.singleton_append]
  apply Derives.append_right _ (List.drop (posx + 1) rule1.output)
  exact hsoundy

/--
Any EarleyItem within an EarleySet is sound.
-/
public theorem soundItemEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (x : EarleyItem T G.NT) (hmem : x ∈ EarleySet G w) : isSound G w x := by
  induction hmem with
  | init _ hmem =>
    exact soundItemPosZero _ _ hmem
  | scan _ _ _ _ _ _ hx hmem hbounds hw hnext ih =>
    exact soundItemScan _ _ hx hmem hbounds hw hnext ih
  | predict _ _ _ _ _ _ _ hx hmemx hmemr2 hnext hbounds hw =>
    exact soundItemPosZero _ _ hmemr2
  | complete x y rule1 rule2 posx posy i j k hx hmemx hy hmemy hcomp hnext ihx ihy =>
    exact soundItemComplete _ _ hx hmemx hy hmemy hcomp hnext ihx ihy

/--
The soundness criteria for the EarleySet:
Given a finished item for a word within the set,
the grammar has to be able to generate that word.
-/
public theorem soundnessEarley {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    {w : List (Symbol T G.NT)} {x : EarleyItem T G.NT} (hmem : x ∈ EarleySet G w)
    (hfin : isFinished G w x) : G.Generates w := by
  unfold Generates
  have := soundItemEarley G w x hmem
  simp only [isFinished, isComplete, Bool.and_eq_true, beq_iff_eq] at hfin
  simp only [isSound, hfin, slice_length, betaItem, List.drop_length, List.append_nil] at this
  exact this

end Soundness

section Completeness
open ContextFreeRule
open ContextFreeGrammar

/--
A set of Items {(A → α • β, i, j)} is partially complete up to `n`, if

every possible derivation the grammar provides is within the set?

This is not for the full set of EarleyItems

Rau introduces `Derivation` which mainly limits the length of the derivation itself
Im not sure if Derives is enough or I actually need that wrapper as well
-/
public def isPartiallyComplete (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) (I : Set (EarleyItem T G.NT)) : Prop :=
  ∀ (rule : ContextFreeRule T G.NT) (pos i i' j : Nat) (x : EarleyItem T G.NT) (a : Symbol T G.NT),
    i ≤ j ∧ j ≤ n ∧ n ≤ w.length ∧ x = ⟨rule, pos, i, i'⟩ ∧ x ∈ I ∧ nextSymbol x = some a ∧
    G.Derives [a] (slice w i j) → ⟨rule, pos+1, i', j⟩ ∈ I

/--
A set of Items {(A → α • β, i, j)} is partially complete up to `n`, if
every possible derivation the grammar provides is within the set?
TODO
-/
lemma partiallyCompleteUpTo (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) (I : Set (EarleyItem T G.NT))
    {pos i j k : Nat} {A : G.NT} {α : List (Symbol T G.NT)}
    (hjn : j ≤ n) (hlen : n ≤ w.length)
    (x : EarleyItem T G.NT) (hx : x = ⟨⟨A, α⟩, pos, i, k⟩)
    (hmem : x ∈ I) (wfI : ∀ x ∈ I, isWellFormed G w x)
  -- betaItem should just be alpha? right
    (hd : G.Derives α (slice w j n))
    (hcomp : isPartiallyComplete G w n I)--(λD' => length D' <= length D))
    : ⟨⟨A, α⟩, α.length, i, k⟩ ∈ I :=
  sorry

/--
TODO
-/
lemma partiallyCompleteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) : isPartiallyComplete G w n (EarleySet G w) := by
  sorry

/--
The completeness criteria for the EarleySet:
Given a word the grammar can generate,
there has to be a finished item within the corresponding EarleySet.
-/
public theorem completenessEarley {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    {w : List (Symbol T G.NT)} (hw : isWord G w) (hgen : G.Generates w) :
    ∃ x ∈ EarleySet G w, isFinished G w x := by
  simp only [isFinished, isComplete, Bool.and_eq_true, beq_iff_eq]
  have partComp := partiallyCompleteEarley G w w.length
  simp [isPartiallyComplete] at partComp

  simp only [Generates] at hgen
  have := derives_implies_Derivation hgen
  rcases this with ⟨D,hD⟩

  -- need to case on the length of the word. if it is zero, then its trivial
  have rule := D.getLast sorry
  let x : EarleyItem T G.NT := ⟨⟨G.initial, rule.output⟩, rule.output.length, 0, w.length⟩
  use x
  simp [x]
  sorry

end Completeness

/--
The correctness criteria for the EarleySet.

A word can be generated from the grammar
iff
there exists a finished item within the corresponding EarleySet.
-/
public theorem correctnessEarley {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    {w : List (Symbol T G.NT)} (hw : isWord G w) :
    G.Generates w ↔ ∃ x ∈ EarleySet G w, isFinished G w x := by
  constructor
  · intro hgen
    apply completenessEarley hw hgen
  · intro hex
    rcases hex with ⟨hw,h⟩
    apply soundnessEarley h.left h.right

/--
The EarleySet only has a finite number of element.
TODO: seem to need this for the completeness proof already
--have := Fintype.ofFinite α
-/
public theorem finiteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Finite (EarleySet G w) := by
  sorry

end EarleySet

end Invariants
end Earley
