module
public import Mathlib.Computability.ContextFreeGrammar
@[expose] public section

/-!
This module houses the definition of `filterWithIdx`, which enables you to filter a List,
while keeping track of the original indices.

TODO: Lean doesnt have lazyness for linked lists, right?
      But surely there are some optimizations for these kind of chains?
      So it would be a worst-case perf increase since this is basicly a glorified
      .zip(l.length).filter(p)?
      but without lemmas, this is easier to reason with by induction hm
-/

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

end Utils
end Earley
