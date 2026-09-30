-- Prove2me | solution 1 for lean_workbook_plus_78362
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:41:36.847302+00:00
-- url     : https://prove2.me/submissions/93361d78-2516-4346-b16d-ab6da8560701

import Mathlib

theorem quartic_young (x y : ℝ) : 4*x^3*y ≤ 3*x^4+y^4 := by
  have h : 0 ≤ (x-y)^2*((x+y)^2+2*x^2) := by positivity
  nlinarith only [h]

theorem quartic_young_equality (x y : ℝ) : 3*x^4+y^4 = 4*x^3*y ↔ x = y := by
  constructor
  · intro h
    have hz : (x-y)^2*((x+y)^2+2*x^2) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
    · have hx : x^2 = 0 := by nlinarith only [h2, sq_nonneg (x+y), sq_nonneg x]
      have hx0 : x = 0 := sq_eq_zero_iff.mp hx
      rw [hx0] at h2
      have hy0 : y = 0 := by nlinarith only [h2, sq_nonneg y]
      exact hx0.trans hy0.symm
  · rintro rfl
    ring

theorem solution (x y z : ℝ) :
    3*x^4+y^4 ≥ 4*x^3*y ∧ 3*y^4+z^4 ≥ 4*y^3*z ∧ 3*z^4+x^4 ≥ 4*z^3*x :=
  ⟨quartic_young x y, quartic_young y z, quartic_young z x⟩
