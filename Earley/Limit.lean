module
public import Earley.Model
@[expose] public section

#check Monotone
#check Nat.iterate

def natUnion {α : Type} (f : Nat → Set α) : Set α :=
  sorry
  --{ f n | ∀ n, True }

/--
Applies the function until the result doesn't change and returns that fixpoint.
-/
def limit {α : Type} (f : Set α → Set α) (I : Set α) : Set α :=
  sorry
