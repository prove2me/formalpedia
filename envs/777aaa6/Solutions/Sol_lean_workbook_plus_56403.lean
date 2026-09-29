-- Prove2me | solution 1 for lean_workbook_plus_56403
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:59.434872+00:00
-- url     : https://prove2.me/submissions/9abd3e9d-4e3f-4449-a032-ad361b727558

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (2 * a * b + 1) / (a * b + c^2) + (2 * b * c + 1) / (b * c + a^2) + (2 * c * a + 1) / (c * a + b^2) ≥ 13 / 2 + a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
