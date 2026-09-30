-- Prove2me | solution 1 for lean_workbook_plus_26982
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:12:46.619704+00:00
-- url     : https://prove2.me/submissions/e4940f30-656f-481d-9ca3-0af883e40b36

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (2 * (a + b + c))) ≤ (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ∧ (1 / (b + c) + 1 / (c + a) + 1 / (a + b)) ≤ (1 / 2) * (1 / a + 1 / b + 1 / c) := by
  have hbc : 0 < b + c := by positivity
  have hca : 0 < c + a := by positivity
  have hab : 0 < a + b := by positivity
  constructor
  · rw [div_add_div _ _ hbc.ne' hca.ne', div_add_div _ _ (by positivity) hab.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
      mul_pos (mul_pos ha hb) hc, sq_nonneg (a + b - 2 * c), sq_nonneg (b + c - 2 * a), sq_nonneg (c + a - 2 * b)]
  · have h1 : 1 / (b + c) ≤ (1 / 4) * (1 / b + 1 / c) := by
      rw [div_add_div _ _ hb.ne' hc.ne', ← mul_div_assoc, div_le_div_iff₀ hbc (by positivity)]
      nlinarith [sq_nonneg (b - c)]
    have h2 : 1 / (c + a) ≤ (1 / 4) * (1 / c + 1 / a) := by
      rw [div_add_div _ _ hc.ne' ha.ne', ← mul_div_assoc, div_le_div_iff₀ hca (by positivity)]
      nlinarith [sq_nonneg (c - a)]
    have h3 : 1 / (a + b) ≤ (1 / 4) * (1 / a + 1 / b) := by
      rw [div_add_div _ _ ha.ne' hb.ne', ← mul_div_assoc, div_le_div_iff₀ hab (by positivity)]
      nlinarith [sq_nonneg (a - b)]
    linarith
