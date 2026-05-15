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
A set of EarleyItems {(A → α • β, i, j)} w.r.t to a word `w` is partially complete up to `n`, if
for i ≤ j ≤ n every item in the set `(A → α • a β, i, j)` and
every derivation from `a` to w_j/n,
the set also contains the item `(A → α a • β, i, k)`.

Basicly if there is Derivation within the indices that progresses the word,
the corresponding progressed item has to be within the set as well.

Crucially, there exists a predicate `P` which the Derivation has to uphold.
This is to limit the length of the Derivation.
-/
public def isPartiallyComplete (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) (I : Set (EarleyItem T G.NT)) (P : List (ContextFreeRule T G.NT) → Bool) : Prop :=
  ∀ (rule : ContextFreeRule T G.NT) (pos i j k : Nat) {x : EarleyItem T G.NT} {a : Symbol T G.NT}
    {D : List (ContextFreeRule T G.NT)},
    j ≤ k ∧ k ≤ n ∧ n ≤ w.length ∧ x = ⟨rule, pos, i, j⟩ ∧ x ∈ I ∧
    nextSymbol x = some a ∧ Derivation G [a] D (slice w j k) ∧ P D
    → ⟨rule, pos+1, i, k⟩ ∈ I

/--
If a set of EarleyItems is partially complete up to `n`, then given a progressable item,
the progressed item is also within the set.
See `isPartiallyComplete`.
-/
lemma partiallyCompleteUpTo (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) (I : Set (EarleyItem T G.NT))
    {pos i j : Nat} {A : G.NT} {α : List (Symbol T G.NT)} {D : List (ContextFreeRule T G.NT)}
    (hjn : j ≤ n) (hlen : n ≤ w.length) (x : EarleyItem T G.NT) (hx : x = ⟨⟨A, α⟩, pos, i, j⟩)
    (hmem : x ∈ I) (wfI : ∀ x ∈ I, isWellFormed G w x)
    (hD : Derivation G (betaItem x) D (slice w j n))
    (hcomp : isPartiallyComplete G w n I (fun D' => D'.length ≤ D.length)) :
    ⟨⟨A, α⟩, α.length, i, n⟩ ∈ I := by
  induction hbeta : betaItem x generalizing pos i j n A D α x with
  | nil =>
    -- A → α • []
    -- The position is given and the item is already complete.
    have hpos : pos = α.length := by
      simp [betaItem, hx] at hbeta
      have := wfI x hmem
      simp [isWellFormed, hx] at this
      omega
    simp only [betaItem, hx, hpos, List.drop_length] at hD
    have : slice w j n = [] := Derivation_from_empty G hD
    have heq : j = n := by
      simp [slice_eq_droptake] at this
      omega
    rw [heq, hpos] at hx
    rw [hx] at hmem
    apply hmem
  -- A → α • a β
  | cons r rs ih =>
    rw [hbeta] at hD
    simp only [betaItem, hx] at hbeta
    have wfX := wfI x hmem
    simp [isWellFormed, hx] at wfX
    rw [← List.singleton_append] at hD
    -- Split the Derivation into a single step and the rest
    have := Derivation_cons_split G hD
    rcases this with ⟨a',b',E,F,⟨hE,hF,hab,hlenE,hlenF⟩⟩
    -- XXX: think about the API of the lemma and what I even prove here
    have : ∃ k, a' = slice w j k ∧ b' = slice w k n ∧ j ≤ k ∧ k ≤ n:= by
      sorry
    rcases this with ⟨k,⟨ha',hb',hjk,hkn⟩⟩
    simp only [ha', hb'] at hE hF
    -- Construct an EarleyItem part of the Set, where the next symbol has been parsed
    let y : EarleyItem T G.NT :=  ⟨⟨A,α⟩, pos+1, i, k⟩
    have hnextx : nextSymbol x = some r := by
      simp [nextSymbol, hx]
      have := @List.getElem_cons_drop _ α pos (by grind)
      grind
    have hmemy : y ∈ I := by
      simp only [isPartiallyComplete, decide_eq_true_eq, and_imp] at hcomp
      apply hcomp ⟨A,α⟩ pos i j k (by omega) (by omega) (by omega) hx hmem hnextx hE hlenE
    have hrs : betaItem y = rs := by
      simp only [betaItem, y]
      have := @List.drop_add_one_eq_tail_drop _ pos α
      simp [this, hbeta]
    have wfY := wfI y hmemy
    simp [isWellFormed, y] at wfY
    -- Apply the IH for that Item
    have ih := @ih n (pos+1) i k A α F hkn hlen y (by simp [y]) hmemy
    apply ih
    · simp [hrs, hF]
    -- This is only a more restricted version of `hcomp`
    -- where there are less possible input combinations, and thus trivially correct.
    · simp [isPartiallyComplete] at hcomp
      simp [isPartiallyComplete]
      grind
    · simp [hrs]

/--
The EarleySet is partially complete.
-/
lemma partiallyCompleteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (n : Nat) : isPartiallyComplete G w n (EarleySet G w) (fun _ => true) := by
  intro rule pos i i' j x a D ⟨hij, hjn, hlen, hx, hmemx, hnext, hD, hP⟩
  induction hDlen : D.length generalizing rule pos i i' j x a D with
  | zero =>
      simp at hDlen
      simp only [hDlen, Derivation] at hD
      have hjw : j ≤ w.length := by omega
      have hji : j = i' + 1 := by
        have : [a].length = 1 := by simp
        rw [hD] at this
        exact succ_of_len w i' j this hjw
      have hi'len : i' < w.length := by omega
      have hw : w[i'] = a := by
        have := @slice_one _ w i' (by omega)
        simp [hji, this] at hD
        simp [hD]
      rw [hji]
      apply EarleySet.scan x rule pos i i' a hx hmemx hi'len hw hnext
  | succ m ih => sorry

  -- nat_less_induct
  --induction D.length using Nat.strong_induction_on generalizing rule pos i i' j x a D with
  --| h m ih => sorry

/--
The completeness criteria for the EarleySet:
Given a word the grammar can generate,
there has to be a finished item within the corresponding EarleySet.
-/
public theorem completenessEarley {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    {w : List (Symbol T G.NT)} (hw : isWord G w) (hgen : G.Generates w) :
    ∃ x ∈ EarleySet G w, isFinished G w x := by
  simp only [isFinished, isComplete, Bool.and_eq_true, beq_iff_eq]
  -- Fetch the first rule that has to have been applied
  have := derives_implies_Derivation hgen
  rcases this with ⟨D,hD⟩
  have := rule_from_derives G w hw D hD
  rcases this with ⟨u,D',hu⟩
  -- Create the initial EarleyItem, which is on the critical path
  let x : EarleyItem T G.NT := ⟨⟨G.initial, u⟩, 0, 0, 0⟩
  have hx : x = ⟨⟨G.initial, u⟩, 0, 0, 0⟩ := by simp [x]
  have hmemx : x ∈ EarleySet G w := by
    apply EarleySet.init x.rule hu.right
    simp [hx]
  -- The remaining Derivation links the initial item with the final item via partial completeness
  have hD' : Derivation G u D' (slice w 0 w.length) := by simp [hu.left]
  -- this is only a restricted version of `partiallyCompleteEarley`,
  -- where there are less possible input combinations, and thus trivially correct.
  have partCompShorter :
      isPartiallyComplete G w w.length (EarleySet G w) (fun D => D.length ≤ D'.length) := by
    unfold isPartiallyComplete
    have partComp := partiallyCompleteEarley G w w.length
    simp only [isPartiallyComplete, Std.le_refl, true_and, and_imp] at partComp
    grind
  -- Prove a finished EarleyItem exists by fully leaning on EarleySet being partially completed
  have : ⟨⟨G.initial, u⟩, u.length, 0, w.length⟩ ∈ EarleySet G w := by
    exact partiallyCompleteUpTo G w w.length (EarleySet G w)
      (by omega) (by omega) x hx hmemx (wfEarley G w) hD' partCompShorter
  use ⟨⟨G.initial, u⟩, u.length, 0, w.length⟩

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
  · apply completenessEarley hw
  · intro hex
    rcases hex with ⟨hw,h⟩
    apply soundnessEarley h.left h.right

/--
The EarleySet only has a finite number of element.
TODO: seem to need this for the recognizer proof
--have := Fintype.ofFinite α
-/
public theorem finiteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Finite (EarleySet G w) := by
  sorry

end EarleySet

end Invariants
end Earley
