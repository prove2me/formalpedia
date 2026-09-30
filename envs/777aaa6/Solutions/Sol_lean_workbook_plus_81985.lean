-- Prove2me | solution 1 for lean_workbook_plus_81985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:29.826179+00:00
-- url     : https://prove2.me/submissions/72896428-d25b-4122-8937-ea243df8e06c

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

private theorem cyclic_amgm (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * a * b * c ≤ a ^ 2 * c + b ^ 2 * a + c ^ 2 * b := by
  have hA : 0 ≤ a ^ 2 * c := by positivity
  have hB : 0 ≤ b ^ 2 * a := by positivity
  have hC : 0 ≤ c ^ 2 * b := by positivity
  have hprod : (a ^ 2 * c) ^ (1 / 3 : ℝ) * (b ^ 2 * a) ^ (1 / 3 : ℝ) *
      (c ^ 2 * b) ^ (1 / 3 : ℝ) = a * b * c := by
    rw [← Real.mul_rpow hA hB, ← Real.mul_rpow (mul_nonneg hA hB) hC]
    rw [show a ^ 2 * c * (b ^ 2 * a) * (c ^ 2 * b) = (a * b * c) ^ 3 by ring]
    rw [← Real.rpow_natCast_mul (by positivity) 3]
    norm_num
    exact Real.rpow_one _
  have hg := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hA hB hC (by norm_num)
  rw [hprod] at hg
  linarith

theorem solution (x y z : ℝ) :
    4 * x ^ 4 * z ^ 2 + 4 * y ^ 4 * x ^ 2 + 4 * z ^ 4 * y ^ 2 +
      x ^ 4 * y ^ 2 + z ^ 4 * x ^ 2 + y ^ 4 * z ^ 2 ≥
      15 * x ^ 2 * y ^ 2 * z ^ 2 := by
  have h1 := cyclic_amgm (x ^ 2) (y ^ 2) (z ^ 2)
    (sq_nonneg x) (sq_nonneg y) (sq_nonneg z)
  have h2 := cyclic_amgm (x ^ 2) (z ^ 2) (y ^ 2)
    (sq_nonneg x) (sq_nonneg z) (sq_nonneg y)
  nlinarith only [h1, h2]
