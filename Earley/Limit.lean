/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model

/-!
This module houses definitions around limits for functions that operate on Sets.
It enables reasoning about the fixpoint of such functions.

TODO: Wondering how much of this I can do by simply using `Monotone`.
      Need to check where those lemmas are used and only fill out sorries of what I use.
List of theorems to port:
- natUnion_upperbound -> limit_upperbound, natUnion_subset
- funpower_upperbound -> limit_upperbound
- natUnion_elem -> limit_elem, natUnion_subset
- natUnion_subset -> natUnion_eq
- natUnion_eq -> natUnion_shift
- chain_implies_mono -> natUnion_shift

- setmonotone_implies_chain_funpower -> regular_fixpoint
- natUnion_shift -> regular_fixpoint
- regular_fixpoint -> limit_idempotent

- limit_upperbound -> Rec
- elem_limit_simp -> Rec
- limit_elem -> Rec
- limit_idempotent -> Rec
-/

@[expose] public section

-- TODO: annotate some with grind
--#check Monotone
--#check MonotoneOn
--#check Function.iterate_fixed
--#check Function.iterate_id

namespace Earley
namespace Limit

variable {α β : Type}

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
TODO
-/
@[grind]
def Chain (f : Nat → Set α) : Prop :=
  ∀ i, f i ⊆ f (i + 1)

/--
TODO
-/
@[grind]
def Continuos (f : Set α → Set β) : Prop :=
  ∀ g, Chain g → (Chain (f ∘ g) ∧ f (natUnion g) = natUnion (f ∘ g))

/--
A function that operates on Sets is called regular, if
it is SetMonotone and Continuos. TODO
-/
@[grind]
def Regular (f : Set α → Set α) : Prop :=
  SetMonotone f ∧ Continuos f

/--
The fixpoint of the identity function is the same as applying it once.

TODO: actually amazing that simp is able to close that goal
      but curious that grind is not. Something about defeq?
-/
@[grind =]
theorem limit_id_eq_id (I : Set α) : limit id I = id I := by
  simp [limit, natUnion]

--TODO
---/
--theorem natUnion_upperbound (f : Set α → Set α) (I G : Set α)
--    (h : ⋀ I, I ⊆ G) : f I ⊆ G := by
--  sorry
--
--/--
--TODO
---/
--theorem iterate_upperbound (f : Set α → Set α) (I G : Set α)
--    (h : ⋀ I, I ⊆ G) : f I ⊆ G := by
--  sorry

/--
Applying f again to the limit of a function, doesn't change the result as long as f is regular.
-/
theorem regular_fixpoint (f : Set α → Set α) (I : Set α) (h : Regular f) :
    f (limit f I) = limit f I := by
  simp [limit, natUnion]
  simp [Chain, Regular, SetMonotone, Continuos] at h
  sorry

/--
Given a fixpoint for a Set, applying limit to it also returns that fixpoint.
-/
theorem limit_of_fixpoint (f : Set α → Set α) (I : Set α) (h : f I = I) : limit f I = I := by
  have := Function.iterate_fixed h
  simp [limit, natUnion, this]

/--
A limit is idempotent. A fixpoint is a fixpoint.
-/
theorem limit_idempotent (f : Set α → Set α) (I : Set α) (h : Regular f) :
    limit f (limit f I) = limit f I := by
  simp [limit, natUnion]
  sorry

end Limit
end Earley
