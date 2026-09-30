-- Prove2me | solution 1 for lean_workbook_plus_61820
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:08:58.112985+00:00
-- url     : https://prove2.me/submissions/8aed4604-391b-4aac-b21e-0f2bba67cfee

import Mathlib
set_option autoImplicit false

theorem solution (X Y Z x y z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : X^2 + Y^2 + Z^2 + X * Y * Z = 4) (hn : x = (2 * X + Y * Z) / (3 * Y * Z)) (ho : y = (2 * Y + Z * X) / (3 * Z * X)) (hp : z = (2 * Z + X * Y) / (3 * X * Y)) : 1 / x + 1 / y + 1 / z = 3   := by
  have hdX : 2 * X + Y * Z ≠ 0 := ne_of_gt (by positivity)
  have hdY : 2 * Y + Z * X ≠ 0 := ne_of_gt (by positivity)
  have hdZ : 2 * Z + X * Y ≠ 0 := ne_of_gt (by positivity)
  have hpoly :
      3 * Y * Z * (2 * Y + Z * X) * (2 * Z + X * Y) +
      3 * Z * X * (2 * X + Y * Z) * (2 * Z + X * Y) +
      3 * X * Y * (2 * X + Y * Z) * (2 * Y + Z * X) =
      3 * (2 * X + Y * Z) * (2 * Y + Z * X) * (2 * Z + X * Y) := by
    linear_combination 6 * X * Y * Z * h
  rw [hn, ho, hp]
  simp only [one_div_div]
  field_simp [hdX, hdY, hdZ]
  linear_combination (1 / 3 : ℝ) * hpoly

#print axioms solution
