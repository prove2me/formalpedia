-- Prove2me | solution 1 for WorkbookSyntax.plus_79360
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:52.871263+00:00
-- url     : https://prove2.me/submissions/957ccc4b-6238-4aaa-a82c-2e0d12e37cff

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : ∀ n : ℕ, ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1   := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hp : 0 < 2 ^ n := pow_pos (by decide) n
    omega
#print axioms solution
