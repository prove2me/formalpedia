-- Prove2me | solution 1 for lean_workbook_plus_55751
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:12:22.503742+00:00
-- url     : https://prove2.me/submissions/49da655a-315e-4ccb-bf25-4ab7df6e61ca

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, a * b * (a + b) + b * c * (b + c) + c * a * (c + a) + 2 * Real.sqrt (a ^ 2 * b * c * (a + b) * (a + c)) + 2 * Real.sqrt (a * b ^ 2 * c * (b + a) * (b + c)) + 2 * Real.sqrt (a * b * c ^ 2 * (c + a) * (c + b)) ≥ 4 * a * b * c + (a + b) * (b + c) * (c + a)) := by
  intro h
  have := h (-1) (-1) 1
  have e1 : ((-1:ℝ) ^ 2 * (-1) * 1 * (-1 + -1) * (-1 + 1)) = 0 := by norm_num
  have e2 : ((-1:ℝ) * (-1) ^ 2 * 1 * (-1 + -1) * (-1 + 1)) = 0 := by norm_num
  have e3 : ((-1:ℝ) * (-1) * 1 ^ 2 * (1 + -1) * (1 + -1)) = 0 := by norm_num
  rw [e1, e2, e3, Real.sqrt_zero] at this
  linarith
