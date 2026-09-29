-- Prove2me | solution 1 for lean_workbook_plus_8922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:04:52.435441+00:00
-- url     : https://prove2.me/submissions/ed44ac01-9885-45e2-a11f-e35f374a1762

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (x : ℝ) (hx: x >= 1): n * (x ^ 2 - 1) ^ 2 * (2 * x ^ n + 1) + 2 * x ^ n * (x ^ 4 + 4 * x ^ 2 + 3) + 2 * (x ^ 4 - 1) ≥ 0 := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have hx4 : 1 ≤ x^4 := by nlinarith [sq_nonneg (x^2-1)]
  have hlast : 0 ≤ x^4-1 := by linarith
  positivity
