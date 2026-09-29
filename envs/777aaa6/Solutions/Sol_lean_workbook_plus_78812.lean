-- Prove2me | solution 1 for lean_workbook_plus_78812
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:21.246278+00:00
-- url     : https://prove2.me/submissions/df01f454-a81c-45a1-b3ff-edcee6352caa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) (k n : ℕ) (hk : k ≥ 3 * n) : (k * a^2 + (k - n) * b * c + n) / (n * b^2 + (k - n) * b * c + n * c^2) + (k * b^2 + (k - n) * c * a + n) / (n * c^2 + (k - n) * c * a + n * a^2) + (k * c^2 + (k - n) * a * b + n) / (n * a^2 + (k - n) * a * b + n * b^2) ≥ 6 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
