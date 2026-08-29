/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Slice
public import Earley.Derivation
public import Earley.Proofs.Finiteness
public import Earley.Recognizer
public import Earley.Proofs.Recognizer
public import Earley.CachedRecognizerPointers
public import Earley.Proofs.CachedRecognizerPointers
public import Earley.Parser

/-!
This module houses the correctness proofs for the
  _____
 |  __ \
 | |__) |_ _ _ __ ___  ___ _ __
 |  ___/ _` | '__/ __|/ _ \ '__|
 | |  | (_| | |  \__ \  __/ |
 |_|   \__,_|_|  |___/\___|_|


The proofs follow the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Proofs
namespace Parser

section Naive

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Recognizer
open Earley.Proofs.Recognizer
open Earley.Parser
open Utils
open ContextFreeGrammar

variable {T N : Type} [BEq T] [LawfulBEq T] [BEq N] [LawfulBEq (EarleyItem T N)]

section Soundness

/--
Given the existance of a parse tree for a word, the word can be generated from the grammar.
-/
public theorem soundnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (ht : ∃ t, parse Gₗ w = some t) : G.Generates (mapT w) := by
  simp only [parse, Option.dite_none_left_eq_some] at ht
  rcases ht with ⟨t, hnEmpty, ht⟩
  split at ht
  · simp at ht
  · rename_i x idx bins hf
    apply soundnessEarleyList w h
    simp only [recognizeList, decide_eq_true_eq]
    use x.item
    let finalBin := (earleyList Gₗ w).bins[w.size]
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial w.size x.item
    have hmem : (x, idx) ∈ (filterWithIdx finalBin P) := by grind
    have := P_of_filterWithIdx finalBin P hmem
    have := getElem_of_filterWithIdx finalBin P hmem
    grind

end Soundness

section Completeness

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
/--
A call to buildTree for well-formed bins never returns none or even a Tree.leaf.
This follows the structure of buildTree quite closely, and the same termination argument holds.
-/
lemma someNode_of_buildTree (G : ContextFreeGrammarList T N) (w : Array T) (j k : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (hk : k < w.size + 1) (hj : j < bins[k].length)
    (hw : w ≠ #[]) : ∃ d ts, buildTree G w hw bins hbins hwf k hk j hj = some (Tree.node d ts) := by
  unfold buildTree
  simp only [List.append_eq, Option.bind_eq_bind]
  split
  · use Symbol.nonterminal bins[k][j].item.rule.input
    use []
  · rename_i i heq
    have := someNode_of_buildTree G w i (k-1) hbins
    grind [wfPointerAux_of_predPointer]
  · rename_i endIdxA pi pj _ heq
    have := wfPointerAux_of_redPointer hwf _ _ heq
    have := someNode_of_buildTree G w pi endIdxA hbins hwf (by lia) (by lia) hw
    rcases this with ⟨d,ts,ht⟩
    have := someNode_of_buildTree G w pj k hbins hwf (by lia) (by lia) hw
    grind
-- If we go away from the two-dimensional view of the bins to a one-dimensional one,
-- then each recursive call accesses a smaller index of the bin.
termination_by ((bins.toList.map List.length).take k).foldl Add.add 0 + j
decreasing_by
  · rename Nat => i
    rename_i heq
    have := wfPointerAux_of_predPointer hwf _ _ heq
    have : k ≠ 0 := by
      grind [wfPointerAux_of_predPointer]
    have : ((bins.toList.map List.length).take (k - 1)).foldl Add.add 0 + bins[k-1].length =
        ((bins.toList.map List.length).take k).foldl Add.add 0 := by
      have := foldl_add_nth bins.toList 0 (k-1) (by grind)
      grind
    lia
  · rename_i endIdxA pi pj _ _ _ _
    have : endIdxA < k ∨ (endIdxA = k ∧ pi < j) := by grind [wfPointerAux_of_redPointer]
    rcases this with h | h
    · have : ((bins.toList.map List.length).take endIdxA).foldl Add.add 0 + bins[endIdxA].length ≤
             ((bins.toList.map List.length).take k).foldl Add.add 0 := by
        have := foldl_le_of_le (bins.toList.map List.length) 0 k endIdxA (by grind)
        grind
      lia
    · lia
  · rename Nat => pj
    have : pj < j := by grind [wfPointerAux_of_redPointer]
    simp [this]

omit [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)] in
lemma some_of_buildTree (G : ContextFreeGrammarList T N) (w : Array T) (j : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (hj : j < bins[w.size].length) (hw : w ≠ #[]) :
    ∃ t, buildTree G w hw bins hbins hwf w.size (by simp) j hj = some t := by
  have := someNode_of_buildTree G w j w.size hbins hwf (by simp) (by lia) hw
  rcases this with ⟨d, ts, h⟩
  use Tree.node d ts

/--
Given a word can be generated from the grammar, then there also exists a parse tree for that word.
-/
public theorem completenessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) (hgen : G.Generates (mapT w)) :
    ∃ t, parse Gₗ w = some t := by
  have hnEmpty : w ≠ #[] := by
    have := nonEmptyDerives_of_isEpsilonFree heps
    grind [Generates]
  have := completenessEarleyList w h heps hgen
  simp only [recognizeList, decide_eq_true_eq] at this
  simp only [parse, hnEmpty, ↓reduceDIte]
  split
  · rename_i heq
    rcases this with ⟨x,hx⟩
    let P := fun y : EarleyItem T G.NT => isFinished Gₗ.initial w.size y
    grind [notP_of_emptyFilterWithIdx]
  · rename_i x idx bins hf
    apply some_of_buildTree Gₗ w idx

end Completeness

/--
The correctness criteria for the parser:
A word can be generated from the grammar iff there exists a parse tree for that word.
-/
public theorem correctnessParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) :
    G.Generates (mapT w) ↔ ∃ t, parse Gₗ w = some t := by
  grind [soundnessParse, completenessParse]

-- TODO: move these somewhere else
/--
Returns the terminals stored within the parse tree.
-/
def yield : (Tree T N) → List T
| Tree.leaf (Symbol.nonterminal _) => []
| Tree.leaf (Symbol.terminal t) => [t]
| Tree.node _ ts => (ts.map yield).flatten

def root : (Tree T N) → Symbol T N
| Tree.leaf d => d
| Tree.node d _ => d

/--
Each node of the tree has to correspond to a rule of the grammar.
-/
def wfRuleTree (G : ContextFreeGrammarList T N) : Tree T N → Prop
| Tree.leaf _ => True
| Tree.node d ts => (∃ r ∈ G.rules, d = Symbol.nonterminal r.input ∧ (ts.map root = r.output))
  ∧ (∀ t ∈ ts, wfRuleTree G t)

/--
Each node of the tree has to correspond to an item of the grammar.
-/
def wfItemTree (G : ContextFreeGrammarList T N) (x : EarleyItem T N) : Tree T N → Prop
| Tree.leaf _ => True
| Tree.node d ts =>
  (d = Symbol.nonterminal x.rule.input ∧ (ts.map root = x.rule.output.take x.position))
  ∧ (∀ t ∈ ts, wfRuleTree G t)

/--
The tree of an item is well-formed w.r.t. to yield iff it parses what it claims to parse.
-/
def wfYield (w : List T) (x : EarleyItem T N) (t : Tree T N) : Prop :=
  yield t = slice w x.startIdx x.endIdx

lemma yieldBuildTree_eq_word {G : ContextFreeGrammarList T N} {w : Array T} (j k : Nat)
    {bins : EarleyBins T N (w.size + 1)} (hbins : EarleyBins.WF G bins)
    (hwf : EarleyBins.PointerWF bins) (hk : k < w.size + 1)
    (hj : j < bins[k].length) (hw : w ≠ #[])
    {t : Tree T N} (ht : buildTree G w hw bins hbins hwf k hk j hj = some t) :
    wfYield w.toList bins[k][j].item t := by
  fun_induction buildTree G w hw bins hbins hwf k hk j hj with
  | case1 k hk j hj x hpx =>
    simp [wfYield]
    simp at ht
    simp [← ht, yield]
    sorry -- predicts
  | case2 k hk j hj x i hpx hk2 ih =>
    sorry
  | case3 k hk j hj x endIdxA i j' ps hpx inv ih1 ih2 =>
    sorry

-- TODO: if I manage, also extend it to cached : )
public theorem yieldParse_eq_word {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] (w : Array T) {Gₗ : ContextFreeGrammarList T G.NT}
    (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) {t : Tree T G.NT} (ht : parse Gₗ w = some t) :
    -- wf_rule_tree G t
    root t = Symbol.nonterminal Gₗ.initial
    ∧ yield t = w.toList := by
  simp only [parse, Option.dite_none_left_eq_some] at ht
  rcases ht with ⟨hnEmpty, ht⟩
  split at ht
  · simp at ht
  · rename_i x j _ heq
    let finalBin := (earleyList Gₗ w).bins[w.size]
    let P := fun x : BinItem T G.NT => isFinished Gₗ.initial w.size x.item
    have hmem : (x, j) ∈ (filterWithIdx finalBin P) := by grind
    have hfin := P_of_filterWithIdx (earleyList Gₗ w).bins[w.size] P hmem
    have hj : j < List.length finalBin := by grind
    have hx : (earleyList Gₗ w).bins[w.size][j].item = x.item := by
      have := getElem_of_filterWithIdx finalBin P hmem
      grind
    --have : (hwf : EarleyBins.PointerWF bins)  :=
    have hwf := pointerWF_of_earleyList Gₗ w
    have h := yieldBuildTree_eq_word j w.size (earleyList Gₗ w).inv hwf (by lia) hj hnEmpty ht
    simp only [wfYield, hx] at h
    simp only [isFinished, Bool.and_eq_true, beq_iff_eq, P] at hfin

    have : x.item.startIdx = 0 ∧ x.item.endIdx = w.toList.length := by grind
    refine ⟨?_, by grind⟩
    simp [root]
    have : x.item.rule.input = Gₗ.initial := by grind
    -- line 1185, requires wf_rule_tree and wf_item_tree
    sorry

end Naive

section Cached

open Earley.Model
open Earley.Recognizer
open Earley.CachedRecognizerPointers
open Earley.Proofs.CachedRecognizerPointers
open Earley.Parser
open Utils

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)]

public theorem parseCached_eq_parse {G : ContextFreeGrammarList T N} (w : Array T) :
    parseCached G w = parse G w := by
  simp only [parseCached, parse]
  have : rawList (earleyCached G w).bins = (earleyList G w).bins := by
    grind [earleyCachedBins_eq_earleyListBins]
  grind

/--
A refinement proof of correctness for the the same algorithm, but utilizing a cached implementation
to compute the bins.
-/
public theorem correctnessCachedParse {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] [Hashable G.NT] [Hashable (EarleyItem T G.NT)] (w : Array T)
    {Gₗ : ContextFreeGrammarList T G.NT} (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G) :
    G.Generates (mapT w) ↔ ∃ t, parseCached Gₗ w = some t := by
  grind [parseCached_eq_parse, correctnessParse]

/--
A refinement proof of yiled for the the same algorithm, but utilizing a cached implementation
to compute the bins.
-/
public theorem yieldCachedParse_eq_word {G : ContextFreeGrammar T} [BEq G.NT] [LawfulBEq G.NT]
    [LawfulBEq (EarleyItem T G.NT)] [Hashable G.NT] [Hashable (EarleyItem T G.NT)] (w : Array T)
    {Gₗ : ContextFreeGrammarList T G.NT} (h : CFGEqCFGₗ G Gₗ) (heps : isEpsilonFree G)
    {t : Tree T G.NT} (ht : parseCached Gₗ w = some t) :
    -- wf_rule_tree G t -- TODO: if I manage, also extend it to cached : )
    root t = Symbol.nonterminal Gₗ.initial ∧ yield t = w.toList := by
  grind [parseCached_eq_parse, yieldParse_eq_word]

end Cached

end Parser
end Proofs
end Earley
