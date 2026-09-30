-- Prove2me | solution 1 for lean_workbook_plus_28024
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:58.835877+00:00
-- url     : https://prove2.me/submissions/9f04f760-bf6b-4d4d-b36a-985d8a9b0680

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : abs x ≤ 1) (hy : abs y ≤ 1) (hz : abs z ≤ 1) : x*y*z ≥ x + y + z - 2 := by
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hxy : x * y ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx2) (by linarith : (0:ℝ) ≤ 1 + y),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + x) (sub_nonneg.2 hy2)]
  nlinarith [mul_nonneg (sub_nonneg.2 hz2) (sub_nonneg.2 hxy),
    mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 hy2)]
