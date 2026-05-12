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
Returns the set of all nonterminals of a given grammar.

TODO: We cast it to Symbol for usage in `isWord` below. (I think I wont need it anywhere else?)
      Rau's Implementation of `isWord`, but with the types it is way easier
      `nonterminals G ∩ { x | x ∈ w } = ∅`
TODO: most likely should live somewhere else or simply remove it
TODO: very interesting to me that the type was not inferable
-/
public def nonterminals (G : ContextFreeGrammar T) : Set (Symbol T G.NT) :=
  { Symbol.nonterminal G.initial } ∪ Set.image
    (fun rule => Symbol.nonterminal rule.input : ContextFreeRule T G.NT → Symbol T G.NT) G.rules

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
TODO: name? Its some trans thing
-/
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
    (hex : ∃ D, Derivation G u D v) : G.Derives u v := by
  rcases hex with ⟨D,hD⟩
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
  · apply Derivation_implies_derives

/--
Given a Derivation from the starting symbol of a grammar to the word,
we can extract the first rule that has been applied.
-/
lemma rule_from_derives (G : ContextFreeGrammar T) (w : List (Symbol T G.NT)) (hword : isWord G w)
    (D : List (ContextFreeRule T G.NT)) (hD : Derivation G [Symbol.nonterminal G.initial] D w) :
    ∃ α D', Derivation G α D' w  ∧ ⟨G.initial, α⟩ ∈ G.rules  := by
  cases D with
  | nil =>
    -- Unreachable since there would be no rewrite and we impose w to be terminals only
    simp [Derivation] at hD
    simp [isWord,← hD] at hword
  | cons x xs =>
    simp only [Derivation, exists_and_left] at hD
    rcases hD.right with ⟨u, hu⟩
    use u, xs
    simp only [hu, true_and]
    -- TODO: maybe write a lemma that r.Rewrites u v means ⟨u,v⟩ iff length u = 1
    -- since this technicality turned out surprisingly annoying
    have := Rewrites.nonterminal_input_mem hu.left
    have hin : x.input = G.initial := by simp_all
    have hout : x.output = u := by
      have := rewrites_iff.mp hu.left
      rcases this with ⟨p,q,⟨hpqIn,hpqOut⟩⟩
      rw [hin] at hpqIn
      have := (@List.self_eq_append_right _ [Symbol.nonterminal G.initial] q)
      cases p <;> cases q <;> simp at hpqIn
      simp [hpqOut]
    simp [← hin, ← hout, hD]

end Earley
