-- Prove2me | solution 1 for lean_workbook_plus_33562
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:06.706278+00:00
-- url     : https://prove2.me/submissions/746c92b4-8d5b-4431-a041-6aeca5e28d4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a * b + b * c + c * a = 1 → a^2 * b / (a^2 * b + a + b) + b^2 * c / (b^2 * c + b + c) + c^2 * a / (c^2 * a + c + a) ≤ (a^2 + b^2 + c^2) / (7 * Real.sqrt 3 * a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
