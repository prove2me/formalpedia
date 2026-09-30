-- Prove2me | solution 1 for lean_workbook_plus_3131
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:15:00.287853+00:00
-- url     : https://prove2.me/submissions/91bc357c-4c61-41db-bcf0-c938f894dcb2

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : a ≥ b ∧ b ≥ c)
  (h₂ : a + b ≥ 2) :
  1 / (2 * a^2 + 3) + 1 / (2 * b^2 + 3) ≥ 4 / ((a + b)^2 + 6) ↔ (a - b)^2 * ((a + b)^2 + 2 * a * b - 3) ≥ 0 := by
  obtain ⟨ha, hb, hc⟩ := h₀
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hR : (a - b)^2 * ((a + b)^2 + 2 * a * b - 3) ≥ 0 := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith
  have hL : 1 / (2 * a^2 + 3) + 1 / (2 * b^2 + 3) ≥ 4 / ((a + b)^2 + 6) := by
    rw [ge_iff_le, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hR]
  exact ⟨fun _ => hR, fun _ => hL⟩
