-- Prove2me | solution 1 for lean_workbook_plus_44452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:14.966664+00:00
-- url     : https://prove2.me/submissions/82d3c511-bcb1-4d7f-9643-b0cee31b3571

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuarticSharpMinimum

theorem certificate (x : ℝ) :
    256 * (x ^ 4 - x ^ 3 + 1) =
      (4 * x - 3) ^ 2 * ((4 * x + 1) ^ 2 + 2) + 229 := by ring

theorem lower_bound (x : ℝ) : 229 / 256 ≤ x ^ 4 - x ^ 3 + 1 := by
  have hprod := mul_nonneg (sq_nonneg (4 * x - 3))
    (show 0 ≤ (4 * x + 1) ^ 2 + 2 by positivity)
  nlinarith only [certificate x, hprod]

theorem equality_iff (x : ℝ) : x ^ 4 - x ^ 3 + 1 = 229 / 256 ↔ x = 3 / 4 := by
  constructor
  · intro h
    have hp : 0 < (4 * x + 1) ^ 2 + 2 := by positivity
    have hprod : (4 * x - 3) ^ 2 * ((4 * x + 1) ^ 2 + 2) = 0 := by
      nlinarith only [certificate x, h]
    have hsq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hp)
    have hz : 4 * x - 3 = 0 := eq_zero_of_pow_eq_zero hsq
    linarith
  · rintro rfl
    norm_num

end QuarticSharpMinimum

theorem solution (x : ℝ) : x ^ 4 - x ^ 3 + 1 ≥ 0 := by
  have := QuarticSharpMinimum.lower_bound x
  linarith

#print axioms QuarticSharpMinimum.lower_bound
#print axioms QuarticSharpMinimum.equality_iff
#print axioms solution
