-- Prove2me | solution 1 for lean_workbook_plus_5456
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:39.640513+00:00
-- url     : https://prove2.me/submissions/98d164ba-9341-4c21-9705-3195fdd00b41

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℂ) (hx1 : x^2 + x + 1 = 0) (hx2 : x^3 = 1) : x^2015 + x^2016 = -x := by
  have h1 : x ^ 2015 = x ^ 2 := by
    rw [show (2015 : ℕ) = 3 * 671 + 2 from rfl, pow_add, pow_mul, hx2, one_pow, one_mul]
  have h2 : x ^ 2016 = 1 := by
    rw [show (2016 : ℕ) = 3 * 672 from rfl, pow_mul, hx2, one_pow]
  rw [h1, h2]
  linear_combination hx1
