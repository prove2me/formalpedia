-- Prove2me | solution 1 for lean_workbook_plus_52096
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:21.211521+00:00
-- url     : https://prove2.me/submissions/5cb5b0e2-ad4e-48ef-bd2b-7ddda2b0f1d7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) : (6 * a + 6 / b) ^ 2 / 3 ≥ 48 * a / b := by
  simp only [div_eq_mul_inv]
  nlinarith [sq_nonneg (a-b⁻¹)]
