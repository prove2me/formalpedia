-- Prove2me | solution 1 for lean_workbook_plus_58293
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:26:57.574182+00:00
-- url     : https://prove2.me/submissions/596b793f-a0c7-4194-ba21-a2002a80067b

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) : x^2 > x^5 := by
  obtain ⟨h0, h1⟩ := hx
  have hx3 : x ^ 3 < 1 := pow_lt_one₀ h0.le h1 (by norm_num)
  have hx2 : 0 < x ^ 2 := by positivity
  calc x ^ 5 = x ^ 2 * x ^ 3 := by ring
    _ < x ^ 2 * 1 := mul_lt_mul_of_pos_left hx3 hx2
    _ = x ^ 2 := by ring
