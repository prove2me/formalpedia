-- Prove2me | solution 1 for lean_workbook_plus_76615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:33.978302+00:00
-- url     : https://prove2.me/submissions/a9519392-f811-40fa-aa4c-77b4e897c457

import Mathlib

private theorem quartic_factor_pos (x : ℝ) :
    0 < x^4 + 2*x^3 + 3*x^2 + 3*x + 2 := by
  nlinarith only [sq_nonneg (x * (x + 1)), sq_nonneg (x + (3/4 : ℝ))]

private theorem remainder_identity (x : ℝ) :
    x^6 + 2 - (x^3 + x^2 + x) =
      (x - 1)^2 * (x^4 + 2*x^3 + 3*x^2 + 3*x + 2) := by ring

theorem solution (x : ℝ) : x^6 + 2 ≥ x^3 + x^2 + x := by
  apply sub_nonneg.mp
  rw [remainder_identity]
  exact mul_nonneg (sq_nonneg _) (le_of_lt (quartic_factor_pos x))

theorem equality_iff (x : ℝ) : x^6 + 2 = x^3 + x^2 + x ↔ x = 1 := by
  constructor
  · intro h
    have hprod : (x - 1)^2 * (x^4 + 2*x^3 + 3*x^2 + 3*x + 2) = 0 := by
      rw [← remainder_identity, h, sub_self]
    have hsq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (quartic_factor_pos x))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro rfl
    norm_num
