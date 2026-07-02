/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model

/-!
This module houses the definition of `Derivation`, which states that
you can derive `v` from `u` by following given sequence of rules.
-/

@[expose] public section

namespace Earley
namespace Utils

open Earley.Model
open ContextFreeGrammar
open ContextFreeRule

attribute [local grind cases] Rewrites
attribute [local grind .] Rewrites.input_output
attribute [local grind] Produces
attribute [local grind] Derives
attribute [local grind <=] Derives.trans
attribute [local grind <=] Derives.append_left
attribute [local grind <=] Derives.append_right
attribute [local grind] Generates

attribute [local grind =_] List.singleton_append
attribute [local grind .] List.append_cancel_left
attribute [local grind =] List.getElem_cons_drop
attribute [local grind =] List.drop_add_one_eq_tail_drop

variable {T : Type}

/--
Returns if the grammar contains a rule with an empty rhs.
TODO: This is required for completeness, so it makes more sense to have it over ContextFreeGrammar?
-/
@[grind]
def isEpsilonFree (G : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ G.rules, !r.output.isEmpty

/--
Returns if the grammar is able to produce epsilon.
-/
@[simp, grind]
public def nonEmptyDerives (G : ContextFreeGrammar T) : Prop :=
  ∀ s, ¬ G.Derives [s] []

/--
A derivation for a CFG `G` states that `u` can be rewritten to `v` via rewriting using the
given rule list in sequence (List is of finite length).
-/
@[grind]
def Derivation (G : ContextFreeGrammar T) :
    List (Symbol T G.NT) → List (ContextFreeRule T G.NT) → List (Symbol T G.NT) → Prop
  | u, [], v => u = v
  | u, x::xs, v => ∃u', x ∈ G.rules ∧ x.Rewrites u u' ∧ Derivation G u' xs v

/--
If there are no rules to be applied, then the input has to be the same as the output.
-/
@[simp, grind =]
lemma Derivation_of_empty_rule (G : ContextFreeGrammar T) {u v : List (Symbol T G.NT)} :
    Derivation G u [] v ↔ (u = v) := by
  grind

/--
If the input word of a Derivation is the empty list, then the output list has to be empty as well.
-/
@[grind .]
lemma Derivation_of_empty_input (G : ContextFreeGrammar T) {v : List (Symbol T G.NT)}
    {rules : List (ContextFreeRule T G.NT)} (h : Derivation G [] rules v) : v = [] := by
  induction rules with
  | nil =>
    rw [Derivation] at h
    simp [h]
  | cons x xs ih =>
    simp [Derivation] at h
    rcases h.right with ⟨u,hu⟩
    cases hu.left

/--
If the list of rules contains multiple elements, then we can apply the first rule.
-/
@[simp, grind =]
lemma Derivation_succ (G : ContextFreeGrammar T) {u v : List (Symbol T G.NT)}
    {d : ContextFreeRule T G.NT} {D : List (ContextFreeRule T G.NT)} :
    Derivation G u (d :: D) v = (d ∈ G.rules ∧ ∃ x, d.Rewrites u x ∧ Derivation G x D v) := by
  simp [Derivation]

/--
Given a Derivation from `u` to `v` by using `rules` and the grammar producing `w` from `v`,
there exists a Derivation from `u` to `w`, which first applies `rules` and then
some sequence of rules.
-/
@[grind →]
lemma Derivation_trans_produces (G : ContextFreeGrammar T) {u v w : List (Symbol T G.NT)}
    {rules : List (ContextFreeRule T G.NT)} (hu : Derivation G u rules v)
    (hv : G.Produces v w) : ∃ D, Derivation G u (rules ++ D) w := by
  induction rules generalizing u v w with
  | nil =>
    rcases hv with ⟨r, hr⟩
    rw [hu]
    use [r]
    simp [Derivation, hr]
  | cons x xs ih =>
    rcases hu with ⟨u',hu⟩
    have := ih hu.right.right hv
    rcases this with ⟨D,hD⟩
    simp only [List.cons_append, Derivation, hu, true_and]
    use D, u'
    simp [hu, hD]

/--
A given Derivation for rewriting `u` to `v` implies that you can derive `v` from `u`.
-/
lemma Derivation_implies_derives {G : ContextFreeGrammar T} {u v : List (Symbol T G.NT)}
    (D : List (ContextFreeRule T G.NT)) (hD : Derivation G u D v) : G.Derives u v := by
  induction D generalizing u with
  | nil => rw [hD]
  | cons x xs ih => grind

/--
Given that you can derive `v` from `u`, there is a Derivation that rewrites `u` to `v`.
-/
lemma derives_implies_Derivation {G : ContextFreeGrammar T} {u v : List (Symbol T G.NT)}
    (h : G.Derives u v) : ∃ D, Derivation G u D v  := by
  simp only [Derives] at h
  induction h with
  | refl =>
    use []
    simp [Derivation]
  | tail h ih hex =>
    rcases hex with ⟨r, hr⟩
    have := Derivation_trans_produces G hr ih
    rcases this with ⟨D, hD⟩
    use r++D

/--
G derives `u` from `v` if and only if there is a Derivation that rewrites `u` to `v`.
-/
lemma derives_iff_Derivation (G : ContextFreeGrammar T) (u v : List (Symbol T G.NT)) :
    G.Derives u v ↔ ∃ D, Derivation G u D v  := by
  constructor
  · apply derives_implies_Derivation
  · intro hex
    rcases hex with ⟨D,hD⟩
    apply Derivation_implies_derives D hD

/--
Given `r.Rewrites u v` with `length u = 1`, we know that the only meaningful rule could be r=⟨u,v⟩
-/
@[grind →]
lemma rule_of_rewrite_step (G : ContextFreeGrammar T) (r : ContextFreeRule T G.NT)
    {v : List (Symbol T G.NT)} {u : G.NT} (hr : r.Rewrites [Symbol.nonterminal u] v) :
    r = ⟨u,v⟩ := by
  have hin : u = r.input := by grind
  have hout : v = r.output := by grind
  rw [hin, hout]

/--
Given a Derivation starting from a single non terminal symbol to the word,
we can extract the first rule that has been applied and construct the derivation for the rest.
-/
@[grind .]
lemma Derivation_step (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (hword : isWord G w)
    {u : G.NT} (D : List (ContextFreeRule T G.NT)) (hD : Derivation G [Symbol.nonterminal u] D w) :
    ∃ v D', Derivation G v D' w  ∧ ⟨u, v⟩ ∈ G.rules  := by
  cases D <;> grind

/--
Given an equality of List concatenations,
if the length of `a` is smaller or equal to the length of `c`,
then we know that `a` has to be the first `a.length` elements of `c`.
TODO: I'm surprised there doesn't exist a lemma for that
-/
lemma take_of_append_longer {α : Type} {a b c d : List α} (h : a ++ b = c ++ d)
    (hac : a.length ≤ c.length) : a = List.take a.length c := by
  induction a generalizing c with
  | nil => simp
  | cons a as ih =>
    cases c <;> grind

/--
Given an equality of List concatenations,
if the length of `a` is bigger than the length of `c`,
then we know that `a` has to be `c` concatenated with the remaning number of elements.
-/
lemma take_of_append_shorter {α : Type} {d : α} {a b c e : List α} (h : a ++ b = c ++ [d] ++ e)
    (hac : a.length > c.length) : a = c ++ [d] ++ e.take (a.length - c.length - 1) := by
  induction a generalizing c with
  | nil => grind
  | cons a as ih =>
    cases c with
    | nil =>
      simp
      simp at h
      grind
    | cons c cs => grind

/--
Given a Derivation from multiple inputs, we can split up the inputs and
derive their output separetely.
-/
lemma Derivation_cons_split (G : ContextFreeGrammar T) {a b c : List (Symbol T G.NT)}
    {D : List (ContextFreeRule T G.NT)} (hD : Derivation G (a ++ b) D c) :
    ∃ a' b' E F, Derivation G a E a'  ∧ Derivation G b F b'  ∧ c = a' ++ b' ∧
      E.length ≤ D.length ∧ F.length ≤ D.length := by
  induction D generalizing a b with
  | nil => simp_all [Derivation]
  | cons d D ih =>
    simp only [Derivation, exists_and_left] at hD
    rcases hD with ⟨hmemh,⟨ab,⟨hd,hD⟩⟩⟩
    have := Rewrites.exists_parts hd
    rcases this with ⟨x,y,⟨happ,hab1⟩⟩
    by_cases hax : a.length ≤ x.length
    -- b gets rewritten by d
    · have hx : x = x.take a.length ++ x.drop a.length := by simp
      have ha : a = x.take a.length := by grind [take_of_append_longer]
      have hb : b = x.drop a.length ++ [Symbol.nonterminal d.input] ++ y := by grind
      have hab2 : ab = x.take a.length ++ x.drop a.length ++ d.output ++ y := by grind
      simp only [hab1] at hD
      have ih := @ih (x.take a.length) (x.drop a.length ++ d.output ++ y)
      have : x.take a.length ++ (x.drop a.length ++ d.output ++ y)
        = x ++ d.output ++ y := by grind
      rw [this] at ih
      clear this
      have := ih hD
      clear ih
      rcases this with ⟨a',b',E,F,⟨hE,hF,hc,hlenE,hlenF⟩⟩
      use a', b', E, d::F
      refine ⟨?_,?_,hc,by simp; omega,by simp [hlenF]⟩
      · rw [ha]
        exact hE
      · simp only [Derivation_succ]
        refine ⟨hmemh,?_⟩
        use x.drop a.length ++ d.output ++ y
        refine ⟨?_,hF⟩
        rw [hb]
        apply rewrites_of_exists_parts
    -- a gets rewritten by d
    · have ha : a = x ++ [Symbol.nonterminal d.input] ++ y.take (a.length - x.length - 1) := by
        grind [take_of_append_shorter]
      have hb : b = y.drop (a.length - x.length - 1) := by grind
      have hab2 : ab = x ++ d.output ++ y.take (a.length - x.length - 1) ++
        y.drop (a.length - x.length - 1) := by grind
      simp only [hab1] at hD
      have ih := @ih (x ++ d.output ++ y.take (a.length - x.length - 1))
        (y.drop (a.length - x.length - 1))
      have : x ++ d.output ++ y.take (a.length - x.length - 1) ++ y.drop (a.length - x.length - 1)
        = x ++ d.output ++ y := by grind
      rw [this] at ih
      clear this
      have := ih hD
      clear ih
      rcases this with ⟨a',b',E,F,⟨hE,hF,hc,hlenE,hlenF⟩⟩
      use a', b', d::E, F
      refine ⟨?_,?_,hc,by simp [hlenE],by simp; omega⟩
      · simp only [Derivation_succ]
        refine ⟨hmemh,?_⟩
        rw [ha]
        use (x ++ d.output ++ List.take (a.length - x.length - 1) y)
        refine ⟨?_,hE⟩
        apply rewrites_of_exists_parts
      · rw [hb]
        exact hF

lemma nonEmptyWordDerivation_of_isEpsilonFree (G : ContextFreeGrammar T) (heps : isEpsilonFree G)
    {a : List (Symbol T G.NT)} (ha : a ≠ []) : ¬ ∃ D, Derivation G a D [] := by
  intro h
  rcases h with ⟨D, hD⟩
  induction D generalizing a with
  | nil => grind
  | cons d D ih =>
    simp at hD
    rcases hD.right with ⟨w,hw⟩
    cases w with
    | nil =>
      have := rewrites_iff.mp hw.left
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.nil_eq,
        List.append_eq_nil_iff, ↓existsAndEq, and_true, true_and] at this
      grind
    | cons _ _ => grind

lemma nonEmptyDerives_of_isEpsilonFree {G : ContextFreeGrammar T} (heps : isEpsilonFree G) :
    nonEmptyDerives G := by
  intro s
  have : [s] ≠ [] := by simp
  have := nonEmptyWordDerivation_of_isEpsilonFree G heps this
  grind [derives_iff_Derivation]

lemma isEpsilonFree_of_nonEmptyDerives (G : ContextFreeGrammar T) (h : nonEmptyDerives G) :
    isEpsilonFree G := by
  by_contra
  simp only [isEpsilonFree, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
    not_forall, exists_prop, Decidable.not_not] at this
  rcases this with ⟨r, hr⟩
  have : G.Derives [Symbol.nonterminal r.input] [] := by grind
  grind

theorem nonEmptyDerives_iff_isEpsilonFree (G : ContextFreeGrammar T) :
    nonEmptyDerives G ↔ isEpsilonFree G := by
  grind [nonEmptyDerives_of_isEpsilonFree, isEpsilonFree_of_nonEmptyDerives]

end Utils
end Earley
