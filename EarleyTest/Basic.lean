example (n : Nat) : n = n := by simp

/--
error: `simp` made no progress
-/
#guard_msgs in
example (n m : Nat) : n = m := by simp

--example (n m : Nat) : n = m := by sorry
