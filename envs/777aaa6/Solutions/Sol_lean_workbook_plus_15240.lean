-- Prove2me | solution 1 for lean_workbook_plus_15240
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:06.633539+00:00
-- url     : https://prove2.me/submissions/6c8688b3-a6d4-4038-bbc2-3c4f3847ccf0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^3 + b^3 + c^3 = 1 / 9 → a^2 + b^2 + c^2 + 1 / (a^2 * b^2) + 1 / (b^2 * c^2) + 1 / (c^2 * a^2) ≥ 730 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
