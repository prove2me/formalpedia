-- Prove2me | solution 1 for lean_workbook_plus_18641
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:08.509531+00:00
-- url     : https://prove2.me/submissions/345f4338-28c1-4bc9-83c2-ce98854c734f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) (habc : a + b + c = 1) (h : a^3 + b^3 + c^3 = a^2 + b^2 + c^2) : (1 / Real.sqrt (a^2 - a * b + b^2) + 1 / Real.sqrt (b^2 - b * c + c^2) + 1 / Real.sqrt (c^2 - c * a + a^2)) ≥ 3 / 2 * Real.sqrt ((a + b) * (b + c) * (c + a) / 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
