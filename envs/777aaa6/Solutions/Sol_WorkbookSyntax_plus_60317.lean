-- Prove2me | solution 1 for WorkbookSyntax.plus_60317
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:20:37.789659+00:00
-- url     : https://prove2.me/submissions/e4e62f00-515a-4a43-9033-c21a3505f615

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution :
  ∑ k ∈ (Finset.range 50), (1 : ℝ) / (k * (k + 1)) = 49 / 50   := by
  norm_num [Finset.sum_range_succ]
#print axioms solution
