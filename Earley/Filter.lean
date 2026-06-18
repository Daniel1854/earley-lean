/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Basic

/-!
This module houses the definition of `filterWithIdx`, which enables you to filter a List,
while keeping track of the original indices.

TODO: Lean doesnt have lazyness for linked lists, right?
      But surely there are some optimizations for these kind of chains?
      So it would be a worst-case perf increase since this is basicly a glorified
      .zip(l.length).filter(p)?
      but without lemmas, this is easier to reason with by induction hm
-/

@[expose] public section

namespace Earley
namespace Utils

variable {α : Type}

/--
TODO
-/
@[grind]
def filterWithIdxAux (P : α → Bool) (i : Nat) : List α → List (α × Nat)
  | [] => []
  | x::xs => if P x
    then (x, i) :: filterWithIdxAux P (i+1) xs
    else filterWithIdxAux P (i+1) xs

/--
TODO
-/
@[grind]
def filterWithIdx (l : List α) (P : α → Bool) : List (α × Nat) :=
  filterWithIdxAux P 0 l

/--
TODO
-/
theorem filterWithIdxAux_eq_zipFilter (l : List α) (P : α → Bool) (i : Nat) :
    filterWithIdxAux P i l = (l.zipIdx i).filter (fun x => P x.1) := by
  induction l generalizing i with
  | nil => grind
  | cons x xs ih => grind

theorem filterWithIdxAux_cong_filter (l : List α) (P : α → Bool) (i : Nat) :
    (filterWithIdxAux P i l).map (fun ⟨item,_⟩ => item) = l.filter P := by
  induction l generalizing i <;> grind

theorem filterWithIdx_cong_filter (l : List α) (P : α → Bool) :
    (filterWithIdx l P).map (fun ⟨item,_⟩ => item) = l.filter P := by
  simp [filterWithIdx, filterWithIdxAux_cong_filter]

lemma filterWithIdxAux_le_length {α : Type} (l : List α) (P : α → Bool) :
    ∀ k ∈ (filterWithIdxAux P 0 l).map Prod.snd, k < l.length := by
  induction l with
  | nil => grind
  | cons x xs ih => grind [filterWithIdxAux_eq_zipFilter]

lemma filterWithIdx_le_length {α : Type} (l : List α) (P : α → Bool) :
    ∀ i ∈ (filterWithIdx l P).map Prod.snd, i < l.length := by
  have := filterWithIdxAux_le_length l P
  grind

end Utils
end Earley
