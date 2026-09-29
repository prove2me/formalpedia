-- Prove2me | solution 1 for lean_workbook_plus_16042
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:58:59.155268+00:00
-- url     : https://prove2.me/submissions/a2ece9b5-aa9b-411e-85c2-6de612268b61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  1 / (a^2 + b * c) ≤ 1 / (a + b)^2 + 1 / (a + c)^2   := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have hd : 0 < a ^ 2 + b * c := by positivity
  have hab : 0 < (a + b) ^ 2 := by positivity
  have hac : 0 < (a + c) ^ 2 := by positivity
  apply (div_le_iff₀ hd).2
  field_simp
  nlinarith [sq_nonneg (a ^ 2 - b * c), mul_nonneg (mul_pos hb hc).le (sq_nonneg (b - c))]
