-- Prove2me | solution 1 for lean_workbook_plus_54915
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:23.266271+00:00
-- url     : https://prove2.me/submissions/57076f71-55fc-41a3-9945-b40c561969a2

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  1 / a^2 + 1 / b^2 ≥ 8 / (a + b)^2 := by
  obtain ⟨ha, hb⟩ := h₀
  have hab : 0 < a * b := mul_pos ha hb
  rw [ge_iff_le, div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ a^2 + b^2) (sq_nonneg (a - b)),
    mul_nonneg hab.le (sq_nonneg (a - b))]
