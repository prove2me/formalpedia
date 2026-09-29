-- Prove2me | solution 1 for lean_workbook_plus_5521
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:24.378099+00:00
-- url     : https://prove2.me/submissions/09ba1de9-6ef6-4252-8d5f-b9f72687d4ce

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y z : ℝ, x ^ 16 + y ^ 16 + z ^ 16 ≥ (x * y) ^ 8 + (y * z) ^ 8 + (z * x) ^ 8 := by
  intro x y z
  simp only [mul_pow]
  nlinarith only [sq_nonneg (x^8-y^8),sq_nonneg (y^8-z^8),sq_nonneg (z^8-x^8)]
