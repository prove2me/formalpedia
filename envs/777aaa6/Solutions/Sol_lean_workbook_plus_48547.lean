-- Prove2me | solution 1 for lean_workbook_plus_48547
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:43.388471+00:00
-- url     : https://prove2.me/submissions/a697f8cb-f766-4769-a094-ecdff96d3331

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 ≤ 1) : a / (a^2 + b * c + 1) + b / (b^2 + c * a + 1) + c / (c^2 + a * b + 1) + 3 * a * b * c < Real.sqrt 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
