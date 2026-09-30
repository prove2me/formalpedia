-- Prove2me | solution 1 for lean_workbook_plus_30747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:40:58.065035+00:00
-- url     : https://prove2.me/submissions/6ff75fb8-819b-420b-9148-a3e29d5f8a10

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ)
  (h₀ : a^2 + b^2 + c^2 = a * b + b * c + c * a)
  (h₁ : (c - a)^3 - (a - b)^3 = 0) :
  a = b ∧ b = c := by
  have hsum : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by nlinarith
  have h1 : (a - b) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : (b - c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  constructor
  · nlinarith [pow_eq_zero_iff (n := 2) (a := a - b) (by norm_num) |>.mp h1]
  · nlinarith [pow_eq_zero_iff (n := 2) (a := b - c) (by norm_num) |>.mp h2]
