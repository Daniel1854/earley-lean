/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Fixpoint
public import Earley.Recognizer
public import Earley.Filter

/-!
This module represents a functional implementation of the Earley algorithm on the production of
a parse tree from bins after recognizing a word. See `Recognizer.lean` for more details on the bins.

The implementation and its proofs follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

@[expose] public section

namespace Earley
namespace Parser

open Earley.Model
open Earley.Model.EarleyItem
open Earley.Fixpoint
open Earley.Recognizer
open Earley.Utils

variable {T N : Type} [BEq T] [BEq N]

/--
The basic tree data structure with no limit on its successors.
-/
inductive Tree (T N : Type) where
  /--
  A leaf with data, but no successors.
  -/
  | leaf (data : Symbol T N) : Tree T N
  /--
  A node with data and its successors.
  -/
  | node (data : Symbol T N) (succ : List (Tree T N)) : Tree T N
deriving BEq, Repr

-- TODO: this should probably live somewhere else.
instance [ToString T] [ToString N] : ToString (Symbol T N) where
 toString sym := match sym with
   | Symbol.terminal t => toString t
   | Symbol.nonterminal nt => toString nt

mutual
  /--
  Accumulates a graphviz string for a list of trees and returns the indices of each of these.
  -/
  def toGraphvizAuxList [ToString T] [ToString N] (acc : String) (idx : Nat)
      (accChildren : List Nat) : List (Tree T N) → String × Nat × List Nat
    | [] => ⟨acc,idx,accChildren⟩
    | t::ts =>
      let ⟨acc,newIdx⟩ := toGraphvizAux acc idx t
      let accChildren := accChildren.append [idx]
      toGraphvizAuxList acc newIdx accChildren ts

  /--
  Accumulates a graphviz string for a tree.
  -/
  def toGraphvizAux [ToString T] [ToString N] (acc : String) (idx : Nat) : Tree T N → String × Nat
    | Tree.leaf d => ⟨acc ++ s!"\n  {idx} [label=\"{d}\", shape=circle];", (idx+1)⟩
    | Tree.node d ts =>
      let node := s!"\n  {idx} [label=\"{d}\", shape=circle];"
      let ⟨acc, newIdx, childIndices⟩ := toGraphvizAuxList (acc ++ node) (idx+1) [] ts
      -- Create an edge from the node to all of its direct children
      let edges := String.join (childIndices.map (fun i => s!"\n  {idx} -> {i};"))
      ⟨acc ++ edges, newIdx⟩
end

/--
Transform a tree into a graphviz compatible format.
-/
def toGraphviz [ToString T] [ToString N] (t : Tree T N) : String :=
  let ⟨graph, _⟩ := toGraphvizAux "Digraph tree {" 1 t
  graph ++ "\n}"

-- TODO: A bit curious that grind isn't able to extract that information well
omit [BEq T] [BEq N] in
lemma wfPointerAux_of_redPointer {G : ContextFreeGrammarList T N} {w : List T}
    {endIdxA i j m n : Nat} {ps : List ReductionPointer}
    {bins : EarleyBins T N (w.length + 1)} (hbins : isWellFormedBins G w bins)
    (hm : m < w.length + 1) (hn : n < bins[m].length)
    (h : bins[m][n].pointer = Pointer.reduction ⟨endIdxA, i, j⟩ ps) :
    endIdxA ≤ w.length ∧ j < bins[m].length ∧
    ∀ (h : endIdxA ≤ w.length), i < bins[endIdxA].length ∧
    (endIdxA < m ∨ (endIdxA = m ∧ i < n)) ∧ j < n := by
  have ⟨_, pInv, sInv⟩:= hbins m (by lia)
  simp only [isWellFormedBinPointers, isWellFormedPointer, tsub_le_iff_right] at pInv
  specialize pInv bins[m][n] (by simp)
  simp only [h] at pInv
  simp only [isSoundPointer] at sInv
  specialize sInv n (by grind)
  simp only [h] at sInv
  lia

lemma foldl_add_nth {α : Type} (xs : List (List α)) (m k : Nat) (hk : k < xs.length) :
    ((xs.map List.length).take k).foldl Add.add m + xs[k].length =
    ((xs.map List.length).take (k+1)).foldl Add.add m := by
  induction xs generalizing m k with
  | nil => grind
  | cons x xs ih =>
    if h : k = 0 then
      simp only [h, List.map_cons, List.take_zero, List.foldl_nil, List.getElem_cons_zero, zero_add,
        List.take_succ_cons, List.foldl_cons]
      lia
    else
      have := ih x.length (k-1) (by grind)
      grind

lemma foldl_le_acc (xs : List Nat) (n : Nat) : n ≤ xs.foldl Add.add n := by
  induction xs generalizing n with
  | nil => grind
  | cons head tail ih => grind

lemma foldl_le_of_le (xs : List Nat) (m k j : Nat) (hk : k < xs.length) (hjk : j < k) :
    (xs.take j).foldl Add.add m + xs[j] ≤ (xs.take k).foldl Add.add m := by
  induction xs generalizing m k j with
  | nil => grind
  | cons x xs ih =>
    if h : k = 0 then
      lia
    else if hj : j = 0 then
      simp only [hj, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      have := @List.take_succ_cons _ x xs (k-1)
      grind [foldl_le_acc]
    else
      specialize ih (m+x) (k-1) (j-1) (by grind) (by grind)
      have := @List.take_succ_cons _ x xs (k-1)
      have heq : k - 1 + 1 = k := by lia
      rw [heq] at this
      simp only [this, List.foldl_cons, ge_iff_le]
      have := @List.take_succ_cons _ x xs (j-1)
      have heq : j - 1 + 1 = j := by lia
      rw [heq] at this
      simp only [this, List.foldl_cons, ge_iff_le]
      have : j - 1 < xs.length := by grind
      have : (x::xs)[j] = xs[j-1] := by grind
      rw [this]
      apply ih

/--
Reconstruct the parse tree by searching the origin data from the EarleyBins.
-/
public def buildTree (G : ContextFreeGrammarList T N) (w : List T) (hw : w ≠ [])
    (bins : EarleyBins T N (w.length + 1)) (inv : isWellFormedBins G w bins) (k : Nat)
    (hk : k < w.length + 1) (j : Nat) (hj : j < bins[k].length) : Option (Tree T N) :=
  let binItem := bins[k][j]
  match hp : binItem.pointer with
  | .null =>
    -- Start building a subtree
    some (Tree.node (Symbol.nonterminal binItem.item.rule.input) [])
  | .predecessor i => do
    -- Add sub tree starting from terminal
    have : k - 1 < w.length := by grind
    have : i < bins[k - 1].length := by grind
    let t ← buildTree G w hw bins inv (k-1) (by lia) i this
    match t with
    | Tree.leaf d => none
    | Tree.node d ts =>
      some (Tree.node d (ts.append [Tree.leaf (Symbol.terminal w[k-1])]))
  | .reduction ⟨endIdxA,i,j⟩ ps => do
    -- We simply take the first possible parse tree.
    have := wfPointerAux_of_redPointer inv _ _ hp
    let t ← buildTree G w hw bins inv endIdxA (by lia) i (by lia)
    match t with
    | Tree.leaf d => none
    | Tree.node d ts => do
      let t ← buildTree G w hw bins inv k (by lia) j (by lia)
      some (Tree.node d (ts.append [t]))
-- Idea: if we go think of the two-dimensional bins as a continuous one-dimensional one,
-- then each recursive call accesses a smaller index of the bin.
termination_by ((bins.toList.map List.length).take k).foldl Add.add 0 + j
decreasing_by
  · have : k ≠ 0 := by grind
    have : ((bins.toList.map List.length).take (k - 1)).foldl Add.add 0 + bins[k-1].length =
        ((bins.toList.map List.length).take k).foldl Add.add 0 := by
      have := foldl_add_nth bins.toList 0 (k-1) (by grind)
      grind
    lia
  · rename Nat => pj
    have : endIdxA < k ∨ (endIdxA = k ∧ i < j) := by grind [wfPointerAux_of_redPointer]
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

/--
Tries to parse a word with given grammar, and returns a parse tree if succesful.
-/
public def parse [LawfulBEq (EarleyItem T N)] (G : ContextFreeGrammarList T N) (w : List T) :
    Option (Tree T N) :=
  -- TODO: strictly speaking, this can be inferred from the result of earleyList,
  --       but this is easier to split upon for now.
  if hw : w = [] then
    none
  else
    let ⟨bins, inv⟩ := earleyList G w
    -- Find the finished item, and follow its pointers.
    let P := fun x => isFinished G.initial (mapT w) x.item
    match h : filterWithIdx bins[w.length] P with
    | [] => none
    | (_, i)::_ =>
      have := filterWithIdx_le_length bins[w.length] P i (by grind)
      buildTree G w hw bins inv w.length (by simp) i this

end Parser
end Earley
