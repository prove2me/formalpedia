-- Prove2me | solution 2 for lean_workbook_plus_64602
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:22.246314+00:00
-- url     : https://prove2.me/submissions/c732ce61-05af-4cac-88b0-5f0317265c69

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 + b^2 - a * b = c^2) : (a - c) * (b - c) ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
