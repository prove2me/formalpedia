-- Prove2me | solution 1 for lean_workbook_plus_51211
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:00.807948+00:00
-- url     : https://prove2.me/submissions/d0299a73-d844-4338-867c-64e9d9382fd8

import Mathlib.Analysis.Complex.Basic

theorem solution  (x y : ℝ) :
  Real.sqrt (2 * x^2 + y^2) ≥ (2 * x + y) / Real.sqrt 3 := by
  have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [ge_iff_le, div_le_iff₀ h3, ← Real.sqrt_mul (by positivity)]
  have hsq : (2 * x + y) ^ 2 ≤ (2 * x ^ 2 + y ^ 2) * 3 := by nlinarith [sq_nonneg (x - y)]
  calc 2 * x + y ≤ |2 * x + y| := le_abs_self _
    _ ≤ Real.sqrt ((2 * x ^ 2 + y ^ 2) * 3) := Real.abs_le_sqrt hsq
