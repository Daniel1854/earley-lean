/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Finite.Prod
public import Earley.Model
public import Earley.Proofs.Model

/-!
This module houses proofs surrounding Finiteness of EarleyItems

The proofs follow the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31

TODO: Rename a ton of lemmas since I forgot about the style in the middle /o\
      https://leanprover-community.github.io/contribute/naming.html
-/

@[expose] public section

namespace Earley
namespace Proofs
namespace Finiteness

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Proofs.Model
open ContextFreeRule
open ContextFreeGrammar

variable {T N : Type}
/--
Takes a Prod and turns it into an EarleyItem.
-/
def itemIntro (input : (ContextFreeRule T N × ℕ × ℕ × ℕ)) : EarleyItem T N :=
  ⟨input.1,input.2.1,input.2.2.1,input.2.2.2⟩

/--
There is only a finite number of well-formed EarleyItems for a specific non-empty grammar and word.

In essence we define the superset of all possible EarleyItems ⟨rule, pos, i, j⟩.
Due the WellFormed-constraints, this results in a Product Set `Top` of
- all rules of G
- all positions for the value range of 0 to the maximum length of any of the rules
- all numbers between 0 and the length of `w` for the indices `i` and `j`

The members of the Product are all individually finite, therefore the Product is also finite.
Since the well-formed EarleyItems are simply a subset of this `Top`, that set also has to be finite.
-/
public theorem finiteEarleyNonEmpty (G : ContextFreeGrammarList T N) (wlen : Nat)
    (hempty : G.rules ≠ []) : Finite { x | isWellFormed G.rules wlen x } := by
  -- The maximum length of any rule
  let M := G.rules.map (fun r => r.output.length) |>.max (by simp [hempty])
  let ruleSet := {x | x ∈ G.rules}
  -- The Set of all possible assignments of an EarleyItem with bounded rule length
  let Top := ruleSet ×ˢ ({i | i ≤ M} ×ˢ  ({i | i ≤ wlen} ×ˢ {i | i ≤ wlen}))
  -- The product of four Finite Sets has to be finite as well.
  have finTop : Finite Top := by
    have hFinMem: Finite ruleSet := by
      simp only [Set.coe_setOf, ruleSet]
      classical
      infer_instance
    infer_instance
  have finImageTop: Finite (Top.image itemIntro) := Finite.Set.finite_image Top itemIntro
  have : { x | isWellFormed G.rules wlen x } ⊆ Top.image itemIntro := by
    intro x hmemx
    have : x.position ≤ M := by
      have wf : isWellFormed G.rules wlen x := by grind
      simp only [isWellFormed] at wf
      have ⟨hmem,hpos,hs,he⟩ := wf
      have : x.rule.output.length ≤ M := by
        have : x.rule.output.length ∈ List.map (fun r => r.output.length) G.rules := by grind
        simp [List.le_max_of_mem this, M]
      lia
    simp only [itemIntro, Set.mem_image, Prod.exists]
    grind [Set.prod]
  exact Finite.Set.subset (Top.image itemIntro) this

/--
There is only a finite number of well-formed EarleyItems for a specific grammar and word.
-/
public theorem finiteEarleyWF (G : ContextFreeGrammarList T N) (wlen : Nat) :
    Finite { x | isWellFormed G.rules wlen x} := by
  cases h : G.rules
  · simp [isWellFormed]
    grind [Finite.exists_equiv_fin, Finite.of_fintype]
  · grind [finiteEarleyNonEmpty]

/--
The EarleySet only has a finite number of elements.

This is a nice theorem to have proven in general, even without any usage,
but this also showcases some annoyance with CFG vs CFGList that I need to work around.
-/
public theorem finiteEarley (G : ContextFreeGrammar T) [BEq G.NT] (w : List (Symbol T G.NT)) :
    Finite (EarleySet G w) := by
  have hwf := wfEarley G w
  have hsub : EarleySet G w ⊆ { x | isWellFormed G.rules w.length x } := by grind
  have : G.rules.toList.Nodup := Finset.nodup_toList G.rules
  let G' : ContextFreeGrammarList T G.NT := ⟨G.initial, G.rules.toList, this⟩
  have hsub' : EarleySet G w ⊆ { x | isWellFormed G'.rules w.length x } := by
    grind [Finset.mem_toList]
  have hf := finiteEarleyWF G' w.length
  exact Set.Finite.subset hf hsub'

end Finiteness
end Proofs
end Earley
