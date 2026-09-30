-- Prove2me | solution 1 for lean_workbook_plus_46726
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:28:26.036588+00:00
-- url     : https://prove2.me/submissions/98e2361e-aee5-418e-a82c-cdddf30a4dd9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / (a + 3) + b / (a * b + 2) + 1 / (b * (b + 2)) > 3 / 5 := by
  have h1 : 0 < a + 3 := by linarith
  have h2 : 0 < a * b + 2 := by positivity
  have h3 : 0 < b * (b + 2) := by positivity
  have key : a / (a + 3) + b / (a * b + 2) + 1 / (b * (b + 2)) - 3 / 5
      = (30 - 36*b + 12*b^2 + 15*b^3 + 10*a + 23*a*b - 4*a*b^2 - 4*a*b^3 + 5*a^2*b
          + 4*a^2*b^2 + 2*a^2*b^3) / (5 * ((a + 3) * (a * b + 2) * (b * (b + 2)))) := by
    field_simp
    ring
  have hP : 0 < 30 - 36*b + 12*b^2 + 15*b^3 + 10*a + 23*a*b - 4*a*b^2 - 4*a*b^3 + 5*a^2*b
          + 4*a^2*b^2 + 2*a^2*b^3 := by
    nlinarith [mul_nonneg (pow_nonneg hb.le 3) (sq_nonneg (a - 1)),
      mul_nonneg (sq_nonneg b) (sq_nonneg (a - 1/2)), pow_pos hb 3, sq_nonneg (b - 3/2),
      mul_pos ha hb, mul_pos (mul_pos ha ha) hb, sq_nonneg b]
  have : 0 < (30 - 36*b + 12*b^2 + 15*b^3 + 10*a + 23*a*b - 4*a*b^2 - 4*a*b^3 + 5*a^2*b
          + 4*a^2*b^2 + 2*a^2*b^3) / (5 * ((a + 3) * (a * b + 2) * (b * (b + 2)))) :=
    div_pos hP (by positivity)
  linarith
