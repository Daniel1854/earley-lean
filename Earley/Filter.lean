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
-/

@[expose] public section

namespace Earley
namespace Utils

variable {α : Type}

@[grind]
def filterWithIdxAux (P : α → Bool) (i : Nat) : List α → List (α × Nat)
  | [] => []
  | x::xs => if P x
    then (x, i) :: filterWithIdxAux P (i+1) xs
    else filterWithIdxAux P (i+1) xs

@[grind]
def filterWithIdx (l : List α) (P : α → Bool) : List (α × Nat) :=
  filterWithIdxAux P 0 l

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

theorem P_of_filterWithIdxAux {x : α} {i n : Nat} (l : List α) (P : α → Bool)
    (hmem : (x, n) ∈ filterWithIdxAux P i l) : P x := by
  induction l generalizing i with
  | nil => grind
  | cons head tail ih => grind

theorem P_of_filterWithIdx {x : α} {n : Nat} (l : List α) (P : α → Bool)
    (hmem : (x, n) ∈ filterWithIdx l P) : P x := by
  grind [P_of_filterWithIdxAux]

lemma filterWithIdxAuxI_le_getElem {α : Type} (l : List α) (i : Nat) (P : α → Bool) :
    ∀ k ∈ (filterWithIdxAux P i l).map Prod.snd, i ≤ k := by
  induction l generalizing i with
  | nil => grind
  | cons x xs ih => grind

theorem getElem_of_filterWithIdxAux {x : α} {i n : Nat} (l : List α) (P : α → Bool)
    (hmem : (x, n) ∈ filterWithIdxAux P i l) : l[n - i]? = some x := by
  induction l generalizing i with
  | nil => grind
  | cons y ys ih =>
    if heq : x = y  then
      grind
    else
      have : (x, n) ∈ filterWithIdxAux P (i+1) ys := by grind
      have := ih this
      have : i + 1 ≤ n := by
        have := filterWithIdxAuxI_le_getElem ys (i+1) P n (by grind)
        grind
      grind

theorem getElem_of_filterWithIdx {x : α} {n : Nat} (l : List α) (P : α → Bool)
    (hmem : (x, n) ∈ filterWithIdx l P) : l[n]? = some x := by
  rw [filterWithIdx] at hmem
  apply getElem_of_filterWithIdxAux l P hmem

theorem memFilterWithIdxAux_of_mem {x : α} (i : Nat) {l : List α} {P : α → Bool}
    (hmem : x ∈ l) (hp : P x) : ∃ n, (x, n) ∈ filterWithIdxAux P i l := by
  induction l generalizing i with
  | nil => grind
  | cons y ys ih =>
    specialize ih (i+1)
    grind

-- TODO: unused
theorem memFilterWithIdx_of_mem {x : α} {l : List α} (P : α → Bool)
    (hmem : x ∈ l) (hp : P x) : ∃ n, (x, n) ∈ filterWithIdx l P := by
  rw [filterWithIdx]
  apply memFilterWithIdxAux_of_mem 0 hmem hp

-- TODO: unused
theorem memFilterWithIdxAux_of_getElem {x : α} (i k : Nat) {l : List α} {P : α → Bool}
    (hk : k < l.length) (hx : x = l[k]) (hp : P x) : (x, k+i) ∈ filterWithIdxAux P i l := by
  induction l generalizing i k with
  | nil => grind
  | cons y ys ih =>
    specialize ih (i+1)
    grind

theorem mem_of_memFilterWithIdxAux {x : α} {i n : Nat} {l : List α} {P : α → Bool}
    (hmem : (x, n) ∈ filterWithIdxAux P i l) : x ∈ l := by
  induction l generalizing i with
  | nil => grind
  | cons y ys ih => grind

theorem mem_of_memFilterWithIdx {x : α} {n : Nat} {l : List α} {P : α → Bool}
    (hmem : (x, n) ∈ filterWithIdx l P) : x ∈ l := by
  rw [filterWithIdx] at hmem
  apply mem_of_memFilterWithIdxAux hmem

theorem notP_of_emptyFilterWithIdxAux {x : α} {i : Nat} {l : List α} {P : α → Bool}
    (hempty : filterWithIdxAux P i l = []) (hP : P x) : x ∉ l := by
  induction l generalizing i with
  | nil => grind
  | cons y ys ih => grind

theorem notP_of_emptyFilterWithIdx {x : α} {l : List α} {P : α → Bool}
    (hempty : filterWithIdx l P = []) (hP : P x) : x  ∉ l := by
  rw [filterWithIdx] at hempty
  apply notP_of_emptyFilterWithIdxAux hempty hP

-- TODO: unused
theorem emptyFilterWithIdxAux_of_notP {i : Nat} {l : List α} {P : α → Bool}
    (h : ∀ x ∈ l, ¬ P x) : filterWithIdxAux P i l = [] := by
  induction l generalizing i with
  | nil => grind
  | cons y ys ih => grind

-- TODO: unused
theorem emptyFilterWithIdx_of_notP {l : List α} {P : α → Bool} (h : ∀ x ∈ l, ¬ P x) :
    filterWithIdx l P = [] := by
  rw [filterWithIdx]
  apply emptyFilterWithIdxAux_of_notP h

theorem filterWithIdxAux_cons_of_notP {i : Nat} {l : List α} {P : α → Bool} {x : α} (hnP : ¬ P x) :
    filterWithIdxAux P i (l ++ [x]) = filterWithIdxAux P i l := by
  induction l generalizing i with
  | nil => grind
  | cons head tail ih => grind

theorem filterWithIdx_cons_of_notP {l : List α} {P : α → Bool} {x : α} (hnP : ¬ P x) :
    filterWithIdx (l ++ [x]) P = filterWithIdx l P := by
  rw [filterWithIdx]
  grind [filterWithIdxAux_cons_of_notP]

theorem filterWithIdxAux_cons_of_P {i : Nat} {l : List α} {P : α → Bool} {x : α} (hP : P x) :
    filterWithIdxAux P i (l ++ [x]) = filterWithIdxAux P i l ++ [(x, l.length + i)] := by
  induction l generalizing i with
  | nil => grind
  | cons head tail ih => grind

theorem filterWithIdx_cons_of_P {l : List α} {P : α → Bool} {x : α} (hP : P x) :
    filterWithIdx (l ++ [x]) P = filterWithIdx l P ++ [(x, l.length)] := by
  grind [filterWithIdxAux_cons_of_P]

theorem filterWithIdxAux_erase_of_not_P {i : Nat} {x : α} {xs : List α} {P : α → Bool}
    (hnP : ¬ P x) :
    (filterWithIdxAux P i (x :: xs)).map (fun (x, i) => (x, i - 1)) = filterWithIdxAux P i xs := by
  induction xs generalizing i with
  | nil => grind
  | cons head tail ih => grind

theorem filterWithIdx_erase_of_not_P {x : α} {xs : List α} {P : α → Bool} (hnP : ¬ P x) :
    (filterWithIdx (x :: xs) P).map (fun (x, i) => (x, i - 1)) = filterWithIdx xs P := by
  grind [filterWithIdxAux_erase_of_not_P]

theorem filterWithIdxAux_erase_of_P {i : Nat} {x : α} {xs : List α} {P : α → Bool} (hP : P x) :
    (filterWithIdxAux P i (x :: xs)).map (fun (x, i) => (x, i - 1))
    = (x, i-1) :: filterWithIdxAux P i xs := by
  induction xs generalizing i with
  | nil => grind
  | cons x xs ih => grind

theorem filterWithIdx_erase_of_P (x : α) (xs : List α) (P : α → Bool) (hP : P x) :
    (filterWithIdx (x :: xs) P).map (fun (x, i) => (x, i - 1))
    = (x, 0) :: filterWithIdx xs P := by
  grind [filterWithIdxAux_erase_of_P]

end Utils
end Earley
