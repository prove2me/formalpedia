-- Prove2me | solution 1 for lean_workbook_plus_18134
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:26.661143+00:00
-- url     : https://prove2.me/submissions/f24dc03b-d65a-4bfd-9b63-f58eedddd782

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hab : a^2 + a * b + b^2 = 3) : (a^2 - a + 1) * (b^2 - b + 1) ≥ 1 := by
  have hs : (a + b) ^ 2 ≤ 4 := by nlinarith [sq_nonneg (a - b)]
  have h1 : a + b ≤ 2 := by nlinarith
  have h2 : -2 ≤ a + b := by nlinarith
  have key : (a^2 - a + 1) * (b^2 - b + 1) - 1
      = (2 - (a + b)) * (-(a + b)^3 - (a + b)^2 + 4 * (a + b) + 6) := by
    linear_combination ((a^2 + a * b + b^2 - 3) - 2 * (a + b)^2 + (a + b) + 7) * hab
  have hh : 0 ≤ -(a + b)^3 - (a + b)^2 + 4 * (a + b) + 6 := by
    rcases le_or_gt (a + b) 1 with h | h
    · have e : -(a + b)^3 - (a + b)^2 + 4 * (a + b) + 6
          = 2 * ((a + b) + 1)^2 + ((a + b) + 2)^2 * (1 - (a + b)) := by ring
      rw [e]
      have := mul_nonneg (sq_nonneg ((a + b) + 2)) (by linarith : (0:ℝ) ≤ 1 - (a + b))
      nlinarith [sq_nonneg ((a + b) + 1)]
    · have e : -(a + b)^3 - (a + b)^2 + 4 * (a + b) + 6
          = 2 + (2 - (a + b)) * (1 + (a + b)) * (2 + (a + b)) := by ring
      rw [e]
      have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (a + b))
        (by linarith : (0:ℝ) ≤ 1 + (a + b))) (by linarith : (0:ℝ) ≤ 2 + (a + b))
      linarith
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 - (a + b)) hh]
