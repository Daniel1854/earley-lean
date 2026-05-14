module
-- TODO: what exactly do I need to import for the @[simp]/attribute to be recognized?
import Mathlib.Computability.ContextFreeGrammar
@[expose] public section

/-!
This module houses an alternative slice API to `List.extract`.
For some proofs the inductive approach instead of drop/take is easier to reason with?
At least Rau does it, but maybe this is unneeded.
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
  | x::xs, 0, (m+1) => x :: slice xs 0 m
  | _::xs, (n+1), (m+1) => slice xs n m

@[simp]
lemma slice_nil {α : Type} (i j : Nat) : slice ([] : List α) i j = [] := by
  simp [slice]

lemma slice_eq_extract {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = xs.extract i j := by
  induction xs, i, j using slice.induct with
  | case1 => simp
  | case2 => simp [slice]
  | case3 x xs m ih => simp [slice, ih]
  | case4 x xs n m ih => simp [slice, ih]

lemma slice_eq_droptake {α : Type} (xs : List α) (i j : Nat) :
    slice xs i j = List.drop i (List.take j xs) := by
  simp [slice_eq_extract, List.drop_take]

@[simp]
lemma slice_zero {α : Type} (xs : List α) (i : Nat) : slice xs i i = [] := by
  simp [slice_eq_extract]

@[simp]
lemma slice_one {α : Type} (xs : List α) {i : Nat} (h : i < xs.length) :
    slice xs i (i + 1) = [xs[i]] := by
  simp only [slice_eq_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  apply List.take_one_drop_eq_of_lt_length

@[simp]
lemma slice_length {α : Type} (xs : List α) : slice xs 0 xs.length = xs := by
  simp [slice_eq_extract]

lemma slice_aux {α : Type} (x : α) {i j : Nat} (xs : List α) (h : i + 1 ≤ j) :
    slice (x :: xs) (i+1) j = slice xs i (j-1) := by
  have : 0 < j := by omega
  simp [slice_eq_extract]
  omega

lemma slice_concat {α : Type} (xs : List α) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    slice xs i j ++ slice xs j k = slice xs i k := by
  simp only [slice_eq_extract, List.extract_eq_take_drop]
  ext l h
  grind

lemma slice_succ_right {α : Type} (xs : List α) {i j : Nat} (hle : i ≤ j) (hb : j < xs.length) :
    slice xs i (j + 1) = (slice xs i j) ++ [xs[j]] := by
  have := @slice_concat _ xs i j (j+1) (by omega) (by omega)
  rw [← this]
  have := slice_one xs hb
  simp [this]

end Earley
