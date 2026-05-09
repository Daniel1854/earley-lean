module
public import Earley.Earley

/-!
This module houses the correctness proofs for
- Earley Typing Judgements / EarleySet
- Earley Recognizer
- Earley Parser
-/

namespace Earley
namespace Invariants

section EarleySet

section Slice

@[simp]
lemma slice_nil {α : Type} (i j : Nat) : slice ([] : List α) i j = [] := by
  simp [slice]

lemma slice_eq_extract {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = xs.extract i j := by
  induction xs, i, j using slice.induct with
  | case1 => simp
  | case2 => simp [slice]
  | case3 x xs m ih => simp [slice, ih]
  | case4 x xs n m ih => simp [slice, ih]

lemma slice_eq_droptake {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = List.drop i (List.take j xs) := by
  simp [slice_eq_extract, List.drop_take]

@[simp]
lemma slice_zero {α : Type} (xs : List α) (i : Nat) : slice xs i i = [] := by
  simp [slice_eq_extract]

@[simp]
lemma slice_one {α : Type} (xs : List α) {i : Nat} (h : i < xs.length) :
    slice xs i (i + 1) = [xs[i]] := by
  simp only [slice_eq_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  apply List.take_one_drop_eq_of_lt_length

@[simp]
lemma slice_length {α : Type} (xs : List α) : slice xs 0 xs.length = xs := by
  simp [slice_eq_extract]

lemma slice_aux {α : Type} (x : α) {i j : Nat} (xs : List α) (h : i + 1 ≤ j) :
    slice (x :: xs) (i+1) j = slice xs i (j-1) := by
  have : 0 < j := by omega
  simp [slice_eq_extract]
  omega

-- TODO: unclear if I will need this
lemma slice_concat {α : Type} (xs : List α) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    slice xs i j ++ slice xs j k = slice xs i k := by
  induction xs, i, j using slice.induct with
  | case1 => simp
  | case2 => simp_all
  | case3 x xs m ih =>
    have : 0 < k := by omega
    have ih := ih (by omega) (by omega)
    have aux := slice_aux x xs hjk
    simp only [Nat.succ_eq_add_one]
    simp only [slice]
    rw [aux]
    simp [slice_eq_extract, List.take_drop]
    sorry
  | case4 x xs n m ih =>
    have : 0 < k := by omega
    have := slice_aux x xs hjk
    sorry

set_option trace.profiler true
lemma slice_succ_right {α : Type} (xs : List α) {i j : Nat} (hle : i ≤ j) (hb : j < xs.length) :
    slice xs i (j + 1) = (slice xs i j) ++ [xs[j]] := by
  simp only [slice_eq_extract, List.extract_eq_take_drop]
  ext l h
  grind
  --have := @slice_concat _ xs i j (j+1) (by omega) (by omega)
  --rw [← this]
  --have := slice_one xs hb
  --simp [this]

end Slice

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

open ContextFreeRule
open ContextFreeGrammar

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
  have : (slice w i (j + 1) ++ List.drop (pos + 1) rule.output)
      = (slice w i j ++ List.drop pos rule.output) := by
    have wfx := wfEarley G w x hmem
    simp [isWellFormed, hx] at wfx
    have hbounds2 := bounds_of_nextSymbol_eq_some hnext
    simp [hx] at hbounds2
    have := slice_succ_right w wfx.right.right.left hbounds
    simp only [this, hw]
    have := @List.getElem_cons_drop _ rule.output pos (by omega)
    simp only [nextSymbol, hx] at hnext
    have := getElem_of_getElem? hnext
    rcases this with ⟨w,hpos⟩
    rw [← hpos]
    have := @List.getElem_cons_drop _ rule.output pos w
    simp [this]
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
  unfold isSound
  simp only
  have := bounds_of_nextSymbol_eq_some hnext
  simp only [hx] at this
  sorry

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

/--
The completeness criteria for the EarleySet:
Given a word the grammar can generate,
there has to be a finished item within the corresponding EarleySet.
-/
public theorem completenessEarley {G : ContextFreeGrammar T} [BEq G.NT] {w : List (Symbol T G.NT)}
    (hgen : G.Generates w) : ∃ x ∈ EarleySet G w, isFinished G w x := by
  sorry

/--
The correctness criteria for the EarleySet.

A word can be generated from the grammar
iff
there exists a finished item within the corresponding EarleySet.
-/
public theorem correctnessEarley {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    {w : List (Symbol T G.NT)} : G.Generates w ↔ ∃ x ∈ EarleySet G w, isFinished G w x := by
  constructor
  · intro hgen
    apply completenessEarley hgen
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
