-- Prove2me | solution 1 for lean_workbook_plus_57937
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:40.949197+00:00
-- url     : https://prove2.me/submissions/b66a9ba4-751b-478e-9351-5df60c161fcd

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h1 : a>0 ∧ b>0 ∧ c>0 ∧ a * b * c = 1) : 1 / (a * b + a + 1) + 1 / (b * c + b + 1) + 1 / (c * a + c + 1) = 1 := by
  obtain ⟨ha, hb, hc, habc⟩ := h1
  have d1 : a * b + a + 1 ≠ 0 := by positivity
  have d2 : b * c + b + 1 ≠ 0 := by positivity
  have d3 : c * a + c + 1 ≠ 0 := by positivity
  have e2 : 1 / (b * c + b + 1) = a / (a * b + a + 1) := by
    rw [div_eq_div_iff d2 d1]
    linear_combination (-1 : ℝ) * habc
  have e3 : 1 / (c * a + c + 1) = (a * b) / (a * b + a + 1) := by
    rw [div_eq_div_iff d3 d1]
    linear_combination (-(a + 1)) * habc
  rw [e2, e3, ← add_div, ← add_div, div_eq_one_iff_eq d1]
  ring
