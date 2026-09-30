-- Prove2me | solution 1 for lean_workbook_plus_55498
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:42.78291+00:00
-- url     : https://prove2.me/submissions/f12798b2-7ff7-491c-9f40-6f659bdfee5b

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x = 1) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2) = (3 * (x * (y + z - 1) ^ 2 + y * (z + x - 1) ^ 2 + z * (x + y - 1) ^ 2) + 4 * (x + y + z - 2) ^ 2 + x * y * z) / (4 * (y + z) * (z + x) * (x + y)) := by
  have h1 : x + y ≠ 0 := by positivity
  have h2 : y + z ≠ 0 := by positivity
  have h3 : z + x ≠ 0 := by positivity
  rw [div_add_div _ _ h1 h2, div_add_div _ _ (mul_ne_zero h1 h2) h3,
    div_sub_div _ _ (mul_ne_zero (mul_ne_zero h1 h2) h3) (by norm_num : (2:ℝ) ≠ 0),
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination ((-26)*x^3*y + (-26)*x^3*z + (-52)*x^2*y^2 + (-104)*x^2*y*z + (32)*x^2*y
    + (-52)*x^2*z^2 + (32)*x^2*z + (-26)*x*y^3 + (-104)*x*y^2*z + (32)*x*y^2 + (-104)*x*y*z^2
    + (64)*x*y*z + (-26)*x*z^3 + (32)*x*z^2 + (-26)*y^3*z + (-52)*y^2*z^2 + (32)*y^2*z
    + (-26)*y*z^3 + (32)*y*z^2) * h
