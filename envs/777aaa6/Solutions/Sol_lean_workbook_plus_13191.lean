-- Prove2me | solution 1 for lean_workbook_plus_13191
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:24.302676+00:00
-- url     : https://prove2.me/submissions/af721da7-e9ae-45b2-855e-5c00261b2526

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (ha3 : a^3 + 2 * b^3 + 2 * c^3 = a + 2 * b + 2 * c) : a^2 + 2 * b^2 + 2 * c^2 ≤ 5 := by
  nlinarith [mul_nonneg (sq_nonneg (a - 1)) (by linarith : (0:ℝ) ≤ a + 1),
    mul_nonneg (sq_nonneg (b - 1)) (by linarith : (0:ℝ) ≤ b + 1),
    mul_nonneg (sq_nonneg (c - 1)) (by linarith : (0:ℝ) ≤ c + 1)]
