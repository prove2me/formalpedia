-- Prove2me | solution 1 for WorkbookSyntax.plus_47065
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:53.372901+00:00
-- url     : https://prove2.me/submissions/aaab9f5f-fdf9-4a1d-911e-6b420c2482a9

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (p : ℕ) (hp : 1 < p) (n : ℕ) : ∑ k ∈ Finset.range n, p^k < p^n   := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_pos (zero_lt_one.trans hp) n]
#print axioms solution
