-- Prove2me | solution 1 for lean_workbook_plus_36664
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:32:55.200732+00:00
-- url     : https://prove2.me/submissions/fe2353a3-e758-4a46-adc0-3c289e697cd6

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (1 + a^2) * (1 + b^2) = 4) : a + b + a * b ≤ 3 := by
  have hp : a * b ≤ 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a * b + 3)]
  have hs : (a + b) ^ 2 = 4 - (a * b - 1) ^ 2 := by nlinarith
  have hkey : (a + b) ^ 2 ≤ (3 - a * b) ^ 2 := by nlinarith
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_pos (sub_pos.mpr hcon) (by linarith : (0:ℝ) < a + b + (3 - a * b))]
