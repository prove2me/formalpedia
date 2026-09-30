-- Prove2me | solution 1 for lean_workbook_plus_70408
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:32.118698+00:00
-- url     : https://prove2.me/submissions/79335d19-1950-418e-8c96-8a68cb814017

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma prod_le_one (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = 3) : x * y * z ≤ 1 := by
  have hxy : x + y = 3 - z := by linarith
  have hp := mul_nonneg hz (sq_nonneg (x - y))
  have hpair : 0 ≤ z * (x + y) ^ 2 - 4 * x * y * z := by nlinarith only [hp]
  rw [hxy] at hpair
  have hrem := mul_nonneg (sq_nonneg (z - 1)) (show 0 ≤ 4 - z by linarith)
  nlinarith only [hpair, hrem]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / (a + b + c) + 2 / 3) * (b / (a + b + c) + 2 / 3) *
      (c / (a + b + c) + 2 / 3) ≤ 1 := by
  have hS : 0 < a + b + c := by positivity
  apply prod_le_one _ _ _ (by positivity) (by positivity) (by positivity)
  field_simp [ne_of_gt hS] <;> ring

#print axioms solution
