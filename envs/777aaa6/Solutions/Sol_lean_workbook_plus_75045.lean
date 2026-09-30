-- Prove2me | solution 1 for lean_workbook_plus_75045
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T18:33:52.482883+00:00
-- url     : https://prove2.me/submissions/79b278e9-bbc3-43cd-81fa-e4a68411c343

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c d : ℝ, (Real.sqrt (a + 1) + Real.sqrt (b + 1) + Real.sqrt (c + 1) + Real.sqrt (d + 1)) ≥ (Real.sqrt (a * b + 1) + Real.sqrt (b * c + 1) + Real.sqrt (c * d + 1) + Real.sqrt (a * d + 1))) := by
  intro h
  have := h (-1) (-1) (-1) (-1)
  have h0 : Real.sqrt ((-1 : ℝ) + 1) = 0 := by
    rw [show (-1 : ℝ) + 1 = 0 by norm_num]
    exact Real.sqrt_zero
  have h2 : Real.sqrt ((-1 : ℝ) * (-1) + 1) = Real.sqrt 2 := by norm_num
  rw [h0, h2] at this
  have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith
