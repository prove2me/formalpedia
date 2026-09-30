-- Prove2me | solution 1 for lean_workbook_plus_47834
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:12:46.526008+00:00
-- url     : https://prove2.me/submissions/79228d55-385e-4f9b-8913-ef932be5be09

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + b^2 = a^5 + b^5) : a + b ≤ 2 := by
  -- key inequality: 8(a^5+b^5) - (a+b)^3 (a^2+b^2) = (a-b)^2 (7a^3+11a^2b+11ab^2+7b^3) ≥ 0
  have hq : 0 ≤ 7 * a^3 + 11 * a^2 * b + 11 * a * b^2 + 7 * b^3 := by positivity
  have key : (a + b)^3 * (a^2 + b^2) ≤ 8 * (a^5 + b^5) := by
    nlinarith [mul_nonneg (sq_nonneg (a - b)) hq]
  by_contra h
  push_neg at h
  have hs : 4 < (a + b)^2 := by nlinarith
  have hpos : 0 < a^2 + b^2 := by nlinarith [sq_nonneg (a - b)]
  have h8 : 8 < (a + b)^3 := by nlinarith [sq_nonneg (a + b), sq_nonneg (a + b - 2)]
  nlinarith [mul_lt_mul_of_pos_right h8 hpos]
