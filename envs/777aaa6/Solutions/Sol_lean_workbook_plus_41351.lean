-- Prove2me | solution 1 for lean_workbook_plus_41351
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:26:59.46635+00:00
-- url     : https://prove2.me/submissions/18aa7b74-434b-4478-8797-06d3ba210737

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2) := by
  intro a b c ⟨ha, hb, hc⟩
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < a + c := by linarith
  have h3 : 0 < a + b := by linarith
  rw [ge_iff_le, div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (by positivity) h3.ne',
    le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (a - b)) h3.le, mul_nonneg (sq_nonneg (b - c)) h1.le,
    mul_nonneg (sq_nonneg (a - c)) h2.le, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    mul_pos (mul_pos ha hb) hc]
