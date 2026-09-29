-- Prove2me | solution 1 for WorkbookSyntax.plus_48310
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:54.143382+00:00
-- url     : https://prove2.me/submissions/e89d7957-9897-4e8f-8d1c-8cae3939fa57

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (x y : ℤ) (n : ℕ) : (x - y) * (∏ k ∈ Finset.range n, (x ^ (2 ^ k) + y ^ (2 ^ k))) = x ^ (2 ^ n) - y ^ (2 ^ n)   := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, pow_mul, pow_mul]
    linear_combination ih * (x ^ (2 ^ n) + y ^ (2 ^ n))
#print axioms solution
