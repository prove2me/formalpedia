-- Prove2me | solution 1 for lean_workbook_plus_63959
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:24:06.637538+00:00
-- url     : https://prove2.me/submissions/036cae13-5872-472c-8b0b-e764137af6c9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem sixth_quintic_refinement (x : ℝ) :
    (3 : ℝ) / 4 * (x - 1) ^ 2 ≤ x ^ 6 - 2 * (x ^ 5 - x ^ 3 + x) + 1 := by
  have h : 4 * (x ^ 6 - 2 * (x ^ 5 - x ^ 3 + x) + 1) =
      (x - 1) ^ 2 * (2 * x ^ 2 - 1) ^ 2 + 3 * (x - 1) ^ 2 := by ring
  have hp := mul_nonneg (sq_nonneg (x - 1)) (sq_nonneg (2 * x ^ 2 - 1))
  nlinarith only [h, hp]

theorem sixth_quintic_equality (x : ℝ) :
    x ^ 6 = 2 * (x ^ 5 - x ^ 3 + x) - 1 ↔ x = 1 := by
  constructor
  · intro h
    have := sixth_quintic_refinement x
    nlinarith [sq_nonneg (x - 1)]
  · rintro rfl
    ring

theorem solution (x a : ℝ) (h : x ^ 5 - x ^ 3 + x = a) : x ^ 6 ≥ 2 * a - 1 := by
  have := sixth_quintic_refinement x
  nlinarith [sq_nonneg (x - 1)]

#print axioms solution
#print axioms sixth_quintic_refinement
#print axioms sixth_quintic_equality
