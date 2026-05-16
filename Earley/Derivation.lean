module
public import Mathlib.Computability.ContextFreeGrammar
@[expose] public section

/-!
This module houses the definition of `Derivation`, which states that
you can derive `v` from `u` by following given sequence of rules.
-/

namespace Earley

open ContextFreeGrammar
open ContextFreeRule

variable {T : Type} {N : Type}

/--
Returns if a list of symbols includes only terminals of given grammar.
-/
public def isWord (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) : Prop :=
  List.isEmpty (w.filter (fun s => match s with
    | Symbol.terminal _ => false
    | Symbol.nonterminal _ => true
  ))

/--
A derivation for a CFG `G` states that `u` can be rewritten to `v` via rewriting using the
given rule list in sequence (List is of finite length)
I am not sure if there is a cleaner way to state it yet.
Rau also got the index at which he rewrites u, thus the total length of what he rewrites

hmem is new as well since rewrites is decoupled, its way more typey
-/
def Derivation (G : ContextFreeGrammar T) :
    List (Symbol T G.NT) → List (ContextFreeRule T G.NT) → List (Symbol T G.NT) → Prop
  | u, [], v => u = v
  | u, x::xs, v => ∃u', x ∈ G.rules ∧ x.Rewrites u u' ∧ Derivation G u' xs v

/--
If the input word of a Derivation is the empty list, then the output list has to be empty as well.
-/
@[grind →]
lemma Derivation_from_empty (G : ContextFreeGrammar T) {v : List (Symbol T G.NT)}
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
If the list of rules contains of multiple elements, then we can unfold the first application.
-/
@[simp, grind =]
lemma Derivation_succ (G : ContextFreeGrammar T) {u v : List (Symbol T G.NT)}
    {d : ContextFreeRule T G.NT} {D : List (ContextFreeRule T G.NT)} :
    Derivation G u (d :: D) v = (d ∈ G.rules ∧ ∃ x, d.Rewrites u x ∧ Derivation G x D v) := by
  simp [Derivation]

/--
TODO: name? Its some trans thing
-/
@[grind →]
lemma Derivation_produces (G : ContextFreeGrammar T) {u v w : List (Symbol T G.NT)}
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
  | cons x xs ih =>
    rcases hD with ⟨u',hu⟩
    apply Derives.trans (u := u) (v := u') (w := v)
    · apply Produces.single
      use x
      simp [hu]
    · exact ih hu.right.right

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
    have := Derivation_produces G hr ih
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
lemma rule_of_rewrite_step (G : ContextFreeGrammar T) (r : ContextFreeRule T G.NT)
    {v : List (Symbol T G.NT)} {u : G.NT} (hr : r.Rewrites [Symbol.nonterminal u] v) :
    r = ⟨u,v⟩ := by
  have := Rewrites.nonterminal_input_mem hr
  have hin : u = r.input := by simp_all
  have hout : v = r.output := by
    have := rewrites_iff.mp hr
    rcases this with ⟨p,q,⟨hpqIn,hpqOut⟩⟩
    rw [hin] at hpqIn
    have := (@List.self_eq_append_right _ [Symbol.nonterminal G.initial] q)
    cases p <;> cases q <;> simp at hpqIn
    simp [hpqOut]
  rw [hin, hout]

/--
Given a Derivation starting from a single non terminal symbol to the word,
we can extract the first rule that has been applied and construct the derivation for the rest.
-/
lemma Derivation_step (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (hword : isWord G w)
    {u : G.NT} (D : List (ContextFreeRule T G.NT)) (hD : Derivation G [Symbol.nonterminal u] D w) :
    ∃ v D', Derivation G v D' w  ∧ ⟨u, v⟩ ∈ G.rules  := by
  cases D with
  | nil =>
    -- Unreachable since there would be no rewrite and we impose w to be terminals only
    simp [Derivation] at hD
    simp [isWord,← hD] at hword
  | cons x xs =>
    simp only [Derivation, exists_and_left] at hD
    rcases hD.right with ⟨v, hv⟩
    use v, xs
    simp only [hv, true_and]
    have := rule_of_rewrite_step G x hv.left
    rw [← this]
    exact hD.left

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
    · -- maybe?
      -- simp only [List.append_assoc, List.cons_append, List.nil_append,
      --  List.append_eq_append_iff] at happ
      -- maybe ?have ha : a = x.slice 0 a.length := by sorry
      have ha : a = x.take a.length := by sorry
      have hb : b = x.drop a.length ++ [Symbol.nonterminal d.input] ++ y := by sorry
      have hab2 : ab = x.take a.length ++ x.drop a.length ++ d.output ++ y := by
        rw [← ha]
        rw [hab1]
        sorry
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
        sorry
      have hb : b = y.drop (a.length - x.length - 1) := by sorry
      have hab2 : ab = x ++ d.output ++ y.take (a.length - x.length - 1) ++
        y.drop (a.length - x.length - 1) := by sorry
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

end Earley
