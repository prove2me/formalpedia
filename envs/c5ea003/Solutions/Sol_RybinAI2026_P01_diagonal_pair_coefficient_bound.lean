-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:23:24.817621+00:00
-- url     : https://prove2.me/submissions/0c6f637b-8223-4aa5-8110-56e877ae6a1c

import Mathlib

theorem solution {x y A B z : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ^ 2 = x * (1 - y)) (hB : B ^ 2 = y * (1 - x))
    (hz : 0 ≤ z) :
    (x + A * z) ^ 2 + (B + y * z) ^ 2 ≤ (1 + z) ^ 2 := by
  have hAsq : A ^ 2 ≤ 1 - y := by
    rw [hA]
    nlinarith [mul_le_mul_of_nonneg_right hx1 (sub_nonneg.mpr hy1)]
  have hBsq : B ^ 2 ≤ 1 - x := by
    rw [hB]
    nlinarith [mul_le_mul_of_nonneg_right hy1 (sub_nonneg.mpr hx1)]
  have hconst : x ^ 2 + B ^ 2 ≤ 1 := by nlinarith [hBsq]
  have hquad : A ^ 2 + y ^ 2 ≤ 1 := by nlinarith [hAsq]
  have hxy : x + y - x * y ≤ 1 := by
    have := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)
    nlinarith
  have hcross : x * A + y * B ≤ 1 := by
    have h1 := sq_nonneg (x - A)
    have h2 := sq_nonneg (y - B)
    nlinarith [h1, h2, hxy]
  have hlin := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2 * z by positivity)
  have hquad' := mul_le_mul_of_nonneg_left hquad (sq_nonneg z)
  nlinarith
