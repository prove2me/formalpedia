-- Prove2me | solution 1 for lean_workbook_plus_51658
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:20.148414+00:00
-- url     : https://prove2.me/submissions/8feee35a-1945-4718-b6c6-98c1b1dad265

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b : ℝ, Real.sqrt (a * b) ≤ (Real.sqrt 3 * a + b / Real.sqrt 3) / 2) := by
  intro h
  have h1 := h (-1) (-1)
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt ((-1 : ℝ) * (-1)) = 1 := by
    rw [show ((-1 : ℝ) * (-1)) = 1 by norm_num, Real.sqrt_one]
  rw [hsq] at h1
  have h2 : (-1 : ℝ) / Real.sqrt 3 < 0 := div_neg_of_neg_of_pos (by norm_num) hs3
  linarith
