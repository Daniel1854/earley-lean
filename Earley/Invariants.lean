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
TODO: maybe split these up like I did with `soundItemEarley`?
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
Any EarleyItem within an EarleySet produced through the .init constructor is sound.
Since we are the beginning of the rule, we only need to show that the initial NT
derives its α which is exactly the rule
-/
public theorem soundItemInit (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    (rule : ContextFreeRule T G.NT) (hmem : rule ∈ G.rules) : isSound G w ⟨rule,0,0,0⟩ := by
  unfold isSound
  simp only
  apply Produces.single
  use rule
  simp [hmem, Rewrites.input_output]

/--
Any EarleyItem within an EarleySet produced through the .scan constructor is sound.
Since we know that the next symbol is `a`, which matches the next symbol in our rule (β) as well,
we can simply construct a β' from β = a β' and showcase that the production holds
-/
public theorem soundItemScan (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {x : EarleyItem T G.NT} {rule : ContextFreeRule T G.NT} {pos i j : Nat} {a : Symbol T G.NT}
    (hx : x = ⟨rule, pos, i, j⟩) (hmem : x ∈ EarleySet G w) (hbounds : j < w.length)
    (hw : w[j] = a) (hnext : nextSymbol x = some a) : isSound G w ⟨rule,pos+1,i,j+1⟩ := by
  unfold isSound
  simp only
  --simp only [hx] at ih
  let y : EarleyItem T G.NT := ⟨rule,pos+1,i,j+1⟩
  have : a :: betaItem y = betaItem x :=  by
    simp only [betaItem]
    simp only [nextSymbol, hx] at hnext
    have := List.getElem_of_getElem? hnext
    rcases this with ⟨w,hpos⟩
    have := @List.getElem_cons_drop _ rule.output pos w
    rw [hpos] at this
    simp [this,hx,y]
  have : w.extract i (j+1) = w.extract i j ++ [w[j]] := by
    simp
    sorry
  -- ⊢ List.take (j + 1 - i) (List.drop i w) = List.take (j - i) (List.drop i w) ++ [w[j]]
  -- List.take (x+1) hl = List.take (x) hl ++ hl[x]
  --have := List.take_succ_cons
  simp [betaItem]
  simp at this
  have := @List.take_add  _ (List.drop i w) (j-i) 1
  -- have "slice \<omega> i j @ \<beta>_item x = slice \<omega> i (j+1) @ \<beta>_item'"
  simp [Derives]
  simp_all
  sorry

/--
Any EarleyItem within an EarleySet produced through the .predict constructor is sound.
Since the new item `A → •α, j, j` is at the beginning of the rule and w_j/j = [],
we only need to show that A derives α, which is exactly the rule.
TODO: maybe delete the unneccessary hypothesis?
-/
public theorem soundItemPredict (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {x : EarleyItem T G.NT} {rule1 rule2 : ContextFreeRule T G.NT} {pos i j : Nat}
    (_hx : x = ⟨rule1, pos, i, j⟩) (_hmemx : x ∈ EarleySet G w) (hmemr2 : rule2 ∈ G.rules)
    (_hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) {a : Symbol T G.NT}
    (hbounds : j < w.length) (_hw : w[j] = a) : isSound G w ⟨rule2,0,j,j⟩ := by
  unfold isSound
  simp only [List.extract, Nat.sub_self, List.take_zero, betaItem_of_zero, List.nil_append]
  apply Produces.single
  use rule2
  simp [hmemr2, Rewrites.input_output]

/--
Any EarleyItem within an EarleySet produced through the .complete constructor is sound.
TODO
-/
public theorem soundItemComplete (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT))
    {x y : EarleyItem T G.NT} {rule1 rule2 : ContextFreeRule T G.NT} {posx posy i j k : Nat}
    (hx : x = ⟨rule1, posx, i, j⟩) (hmemx : x ∈ EarleySet G w)
    (hy : y = ⟨rule2, posy, j, k⟩) (hmemy : y ∈ EarleySet G w)
    (hcomp : isComplete y) (hnext : nextSymbol x = some (Symbol.nonterminal rule2.input)) :
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
  unfold isSound
  induction hmem with
  | init _ hmem =>
    exact soundItemInit _ _ _ hmem
  | scan _ _ _ _ _ _ hx hmem hbounds hw hnext =>
    exact soundItemScan _ _ hx hmem hbounds hw hnext
  | predict _ _ _ _ _ _ _ hx hmemx hmemr2 hnext hbounds hw =>
    exact soundItemPredict _ _ hx hmemx hmemr2 hnext hbounds hw
  | complete x y rule1 rule2 posx posy i j k hx hmemx hy hmemy hcomp hnext ihx ihy =>
    exact soundItemComplete _ _ hx hmemx hy hmemy hcomp hnext

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
  simp only [isSound, hfin, List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero,
    List.take_length, betaItem, List.drop_length, List.append_nil] at this
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
TODO: seem to need this for the recognizer impl
--have := Fintype.ofFinite α
-/
public theorem finiteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Finite (EarleySet G w) := by
  sorry

end EarleySet

end Invariants
end Earley
