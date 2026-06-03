module
public import Earley.Model
@[expose] public section

/-!
This module houses definitions around limits for functions that operate on Sets.
It enables reasoning about the fixpoint of such functions.
-/

namespace Earley
namespace Limit

variable {α : Type}

/--
Applies the given function for each natural number `n`,
s.t. `n` Sets get computed and finally get union'ed.
-/
@[grind]
def natUnion (f : Nat → Set α) : Set α :=
  { x | forall n, x = f n }.sUnion

/--
Applies the function until the result doesn't change and returns that fixpoint.

TODO: Nat.iterate seems more sensible than Nat.repeat for funpower
-/
@[grind]
def limit (f : Set α → Set α) (I : Set α) : Set α :=
  natUnion (fun n => Nat.iterate f n I)

/--
A function, that operates on sets, is monotone if its application (?image) is a superset of the set.
-/
@[grind]
def SetMonotone (f : Set α → Set α) : Prop :=
  ∀ s, s ⊆ f s

/--
The fixpoint of the identity function is the same as applying it once.

TODO: actually amazing that simp is able to close that goal
-/
@[grind =]
theorem limit_id_eq_id (I : Set α) : limit id I = id I := by
  simp [limit, natUnion]

#check Monotone
#check MonotoneOn
#check Function.iterate_fixed
#check Function.iterate_id

end Limit
end Earley
