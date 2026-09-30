-- Prove2me | solution 1 for lean_workbook_plus_67954
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:18:45.12047+00:00
-- url     : https://prove2.me/submissions/f9817642-c2fd-4f52-b5bb-1abe63337410

import Mathlib

theorem solution (a b c : ℝ) (h : a*b*c = 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 + b^2 + c^2 ≤ a^3 + b^3 + c^3 := by
  have hprod : (a^2)^(1/3 : ℝ) * (b^2)^(1/3 : ℝ) * (c^2)^(1/3 : ℝ) = 1 := by
    rw [← Real.mul_rpow (sq_nonneg a) (sq_nonneg b),
      ← Real.mul_rpow (mul_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c)]
    rw [show a^2*b^2*c^2 = (a*b*c)^2 by ring, h]
    simp only [one_pow, Real.one_rpow]
  have hg := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1/3 : ℝ)) (w₂ := (1/3 : ℝ)) (w₃ := (1/3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (sq_nonneg a) (sq_nonneg b) (sq_nonneg c) (by norm_num)
  rw [hprod] at hg
  have hs : 3 ≤ a^2 + b^2 + c^2 := by linarith only [hg]
  have hA := mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ 2*a + 1 by positivity)
  have hB := mul_nonneg (sq_nonneg (b - 1)) (show 0 ≤ 2*b + 1 by positivity)
  have hC := mul_nonneg (sq_nonneg (c - 1)) (show 0 ≤ 2*c + 1 by positivity)
  nlinarith only [hs, hA, hB, hC]
