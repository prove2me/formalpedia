-- Prove2me | solution 1 for lean_workbook_plus_8296
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:23.780385+00:00
-- url     : https://prove2.me/submissions/8f040808-1f4d-4b21-913e-eedaea069818

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a + b + c + 1 / (a * b * c) ≥ (4 * Real.sqrt 3 / 9) * (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
