module
public import Earley.Model
public import Earley.Fixpoint
public import Earley.Recognizer
public import Earley.Filter
@[expose] public section

/-!
This module represents a functional implementation of the Earley algorithm on the production of
a parse tree from bins after recognizing a word. See `Recognizer.lean` for more details on the bins.

The implementation and its proofs follows the work from Rau et Nipkow:
https://doi.org/10.4230/LIPIcs.ITP.2024.31
-/

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

/--
Reconstruct the parse tree by searching the origin data from the EarleyBins.
TODO: Realistically this should never return none if it gets called with a well-formed bin?
TODO: termination_by binsIdx obv doesnt work, there should be some sort of well-formed reasoning?
-/
public partial def buildTree (w : List T) (bins : EarleyBins T N (w.length + 1)) (binsIdx : Nat)
    (hBins : binsIdx < w.length + 1) (binIdx : Nat) (hBin : binIdx < bins[binsIdx].length) :
    Option (Tree T N) :=
  let binItem := bins[binsIdx][binIdx]
  match binItem.pointer with
  | .null =>
    -- Start building a subtree
    some (Tree.node (Symbol.nonterminal binItem.item.rule.input) [])
  | .predecessor i => do
    -- Add sub tree starting from terminal
    have : i < bins[binsIdx - 1].length := sorry -- sth about well-formed items
    let t ← buildTree w bins (binsIdx-1) (by grind) i this
    match t with
    | Tree.leaf d => none
    | Tree.node d ts =>
      -- this is provable since the recursive call actually returned sth
      have : w.length ≠ 0 := sorry
      have : binsIdx - 1 < w.length := by omega
      some (Tree.node d (ts.append [Tree.leaf (Symbol.terminal w[binsIdx-1])]))
  | .reduction ps =>
    -- Add sub tree starting from non-terminal
    match ps with
    | [] => none
    -- TODO: Any reduction pointer is sufficient since we simply take one of the parse trees.
    | ⟨endIdxA,i,j⟩ :: _ => do
      have hEnd : endIdxA < w.length + 1 := sorry -- sth about well-formed items
      have hi : i < bins[endIdxA].length := sorry -- sth about well-formed items
      let t ← buildTree w bins endIdxA hEnd i hi
      match t with
      | Tree.leaf d => none
      | Tree.node d ts => do
        have hj : j < bins[binsIdx].length := sorry
        let t ← buildTree w bins binsIdx (by grind) j hj
        some (Tree.node d (ts.append [t]))

/--
Tries to parse a word with given grammar, and returns a parse tree if succesful.
-/
public def parse [LawfulBEq (EarleyItem T N)] (G : ContextFreeGrammarList T N) (w : List T) :
    Option (Tree T N) :=
  let ⟨bins, inv⟩ := earleyList G w
  -- Find the finished item, and follow its pointers.
  match filterWithIdx bins[w.length]
    (fun x => isFinished G.initial (w.map Symbol.terminal) x.item) with
  | [] => none
  -- TODO: This will be interesting to prove.
  --       A lot about these indices being well-formed I'd imagine.
  | (_, i)::_ => buildTree w bins w.length (by grind) i sorry

end Parser
end Earley
