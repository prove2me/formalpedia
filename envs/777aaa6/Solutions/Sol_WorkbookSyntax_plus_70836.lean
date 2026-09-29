-- Prove2me | solution 1 for WorkbookSyntax.plus_70836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:49.868776+00:00
-- url     : https://prove2.me/submissions/3f09db68-9fe1-4dc9-92e6-1d914f9cd51d

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (n : ℕ) : ∑ i ∈ Finset.range (n+1), i^3 ≤ n^4   := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]
#print axioms solution
