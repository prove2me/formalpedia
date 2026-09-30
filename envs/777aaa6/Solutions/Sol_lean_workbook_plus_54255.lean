-- Prove2me | solution 1 for lean_workbook_plus_54255
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:08.875456+00:00
-- url     : https://prove2.me/submissions/adaa8260-5035-4cf8-b2b6-26802674e6f8

import Mathlib

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^2 / (x + y) + y^2 / (y + z) + z^2 / (z + x)) ≥ (x + y + z) / 2 := by
  have hsum : 0 < x + y + z := by positivity
  have h := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset (Fin 3)) ![x, y, z]
    (g := ![x + y, y + z, z + x]) (by
      intro i _
      fin_cases i <;> simp <;> positivity)
  norm_num [Fin.sum_univ_succ] at h
  have hratio : (x + y + z) ^ 2 / (x + y + (y + z) + (z + x)) =
      (x + y + z) / 2 := by
    field_simp
    <;> ring
  rw [← hratio]
  change (x + y + z) ^ 2 / (x + y + (y + z) + (z + x)) ≤
    x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x)
  simpa only [add_assoc] using h

#print axioms solution
