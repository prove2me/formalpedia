-- Prove2me | solution 1 for lean_workbook_plus_25990
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:44:36.664353+00:00
-- url     : https://prove2.me/submissions/1b9dd792-4f04-4965-9c40-c97b1bc3367a

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : 1 / (x^2 + x + 1) + 1 / (y^2 + y + 1) + 1 / (z^2 + z + 1) >= 1 := by
  have hA : 0 < x^2 + x + 1 := by positivity
  have hB : 0 < y^2 + y + 1 := by positivity
  have hC : 0 < z^2 + z + 1 := by positivity
  have e1 : x * y * z * (x * y * z) = 1 := by rw [h]; norm_num
  have e2 : x^2 * y^2 * z = x * y := by
    have : x^2 * y^2 * z = (x * y * z) * (x * y) := by ring
    rw [this, h, one_mul]
  have e3 : x^2 * y * z^2 = x * z := by
    have : x^2 * y * z^2 = (x * y * z) * (x * z) := by ring
    rw [this, h, one_mul]
  have e4 : x * y^2 * z^2 = y * z := by
    have : x * y^2 * z^2 = (x * y * z) * (y * z) := by ring
    rw [this, h, one_mul]
  have e5 : x^2 * y * z = x := by
    have : x^2 * y * z = (x * y * z) * x := by ring
    rw [this, h, one_mul]
  have e6 : x * y^2 * z = y := by
    have : x * y^2 * z = (x * y * z) * y := by ring
    rw [this, h, one_mul]
  have e7 : x * y * z^2 = z := by
    have : x * y * z^2 = (x * y * z) * z := by ring
    rw [this, h, one_mul]
  rw [div_add_div _ _ hA.ne' hB.ne', div_add_div _ _ (by positivity) hC.ne', ge_iff_le,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
