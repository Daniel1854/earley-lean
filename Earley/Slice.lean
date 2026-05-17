module
-- TODO: what exactly do I need to import for the @[simp]/attribute to be recognized?
import Mathlib.Computability.ContextFreeGrammar
@[expose] public section

/-!
This module houses an alternative slice API to `List.extract`.
For some proofs the inductive approach instead of drop/take is easier to reason with?
At least Rau does it, but maybe this is unneeded.
TODO: some doc strings on the lemmas
-/

namespace Earley

/--
An inductive definition of `List.extract`, which lends itself easier to proofs.
The first parameter is the List, which is to be sliced.
The second is the start index, and the third is the (exclusive) end index

Examples from the List.extract docstring:
* [0, 1, 2, 3, 4, 5].slice 1 2 = [1]
* [0, 1, 2, 3, 4, 5].slice 2 2 = []
* [0, 1, 2, 3, 4, 5].slice 2 4 = [2, 3]
-/
public def slice {α : Type} : List α → Nat → Nat → List α
  | [], _, _ => []
  | _::_, _, 0 => []
  | x::xs, 0, (j+1) => x :: slice xs 0 j
  | _::xs, (i+1), (j+1) => slice xs i j

@[simp, grind =]
lemma slice_nil {α : Type} (i j : Nat) : slice ([] : List α) i j = [] := by
  simp [slice]

lemma slice_eq_extract {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = xs.extract i j := by
  induction xs, i, j using slice.induct with
  | case1 => simp
  | case2 => simp [slice]
  | case3 x xs j ih => simp [slice, ih]
  | case4 x xs i j ih => simp [slice, ih]

lemma slice_eq_droptake {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = List.drop i (List.take j xs) := by
  simp [slice_eq_extract, List.drop_take]

@[simp, grind =]
lemma slice_zero {α : Type} (xs : List α) (i : Nat) : slice xs i i = [] := by
  simp [slice_eq_extract]

@[simp, grind =]
lemma slice_one {α : Type} (xs : List α) {i : Nat} (h : i < xs.length) :
    slice xs i (i + 1) = [xs[i]] := by
  simp only [slice_eq_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  apply List.take_one_drop_eq_of_lt_length

@[simp, grind =]
lemma slice_length {α : Type} (xs : List α) : slice xs 0 xs.length = xs := by
  simp [slice_eq_extract]

@[grind =]
lemma slice_aux {α : Type} (x : α) {i j : Nat} (xs : List α) (h : i + 1 ≤ j) :
    slice (x :: xs) (i+1) j = slice xs i (j-1) := by
  have : 0 < j := by omega
  simp [slice_eq_extract]
  omega

@[grind =]
lemma slice_concat {α : Type} (xs : List α) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    slice xs i j ++ slice xs j k = slice xs i k := by
  simp only [slice_eq_extract, List.extract_eq_take_drop]
  ext l h
  grind

@[grind =]
lemma slice_succ_right {α : Type} (xs : List α) {i j : Nat} (hle : i ≤ j) (hb : j < xs.length) :
    slice xs i (j + 1) = (slice xs i j) ++ [xs[j]] := by
  have := @slice_concat _ xs i j (j+1) (by omega) (by omega)
  rw [← this]
  have := slice_one xs hb
  simp [this]

@[grind <=]
lemma succ_of_len {α : Type} (xs : List α) (i j : Nat) (h : (slice xs i j).length = 1)
    (hb : j ≤ xs.length) : j = i + 1 := by
  simp [slice_eq_extract] at h
  grind

/--
There always exists a middle-point for a slice to concatenate
-/
@[grind <=]
lemma slice_concat_ex {α : Type} {xs ys zs : List α} {i k : Nat} (h : slice xs i k = ys ++ zs)
    (hik : i ≤ k) : ∃ j, ys = slice xs i j ∧ zs = slice xs j k ∧ i ≤ j ∧ j ≤ k := by
  induction xs, i, k using slice.induct generalizing ys zs with
  | case1 i k =>
    simp [slice] at h
    simp only [h, slice_nil, true_and]
    use k
  | case2 x xs i =>
    simp [slice] at h
    simp [h, slice]
    omega
  | case3 x xs k ih =>
    cases ys with
    | nil =>
      use 0
      simp [slice] at h
      simp [slice, h]
    | cons y ys =>
      simp [slice] at h
      have := ih h.right (by simp)
      rcases this with ⟨j,hj⟩
      use j+1
      simp [h, hj, slice]
  | case4 x xs i k ih =>
    simp only [Nat.succ_eq_add_one, Nat.add_le_add_iff_right] at hik
    have := @ih ys zs h hik
    rcases this with ⟨j,hj⟩
    use j+1
    simp [hj, slice]

end Earley
