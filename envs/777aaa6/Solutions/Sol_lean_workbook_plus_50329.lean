-- Prove2me | solution 1 for lean_workbook_plus_50329
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:34:06.950884+00:00
-- url     : https://prove2.me/submissions/29142d3b-f8aa-4bd6-8eb0-3ba7fc107697

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (a - 2 / b) * (b - 1 / a) = 3 / 2) : a + 2 * b ≥ 2   := by
  have hclear := hab
  field_simp [ha.ne', hb.ne'] at hclear
  have hpoly : (2 * (a * b) - 1) * (a * b - 4) = 0 := by
    nlinarith only [hclear]
  have ht : (1 : ℝ) / 2 <= a * b := by
    rcases mul_eq_zero.mp hpoly with hlow | hhigh <;> linarith
  have hsum : 0 < a + 2 * b := by linarith
  by_contra hn
  have hlt : a + 2 * b < 2 := lt_of_not_ge hn
  have hp : 0 < (2 - (a + 2 * b)) * (2 + (a + 2 * b)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [ht, sq_nonneg (a - 2 * b), hp]

#print axioms solution
