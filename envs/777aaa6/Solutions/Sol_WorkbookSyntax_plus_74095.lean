-- Prove2me | solution 1 for WorkbookSyntax.plus_74095
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:50.730351+00:00
-- url     : https://prove2.me/submissions/b0f409fc-5b28-427f-a6e4-1fda9882d607

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution (n : ℕ) (a : ℕ → ℝ) : 4 * ∑ i ∈ Finset.range n, (a i - 1 / 2)^2 ≥ 0   := by
  positivity
#print axioms solution
