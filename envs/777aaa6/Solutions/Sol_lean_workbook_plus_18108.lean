-- Prove2me | solution 1 for lean_workbook_plus_18108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:21.283807+00:00
-- url     : https://prove2.me/submissions/21ac16f7-cd46-474c-83b6-1640ba1aa7f8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ (x y z: ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
  intro x y z
  nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
