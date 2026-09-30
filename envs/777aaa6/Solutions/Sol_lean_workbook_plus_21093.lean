-- Prove2me | solution 1 for lean_workbook_plus_21093
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:26.996367+00:00
-- url     : https://prove2.me/submissions/a3ea58be-e470-4550-99f3-49490b389b33

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) ↔ 2 * (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 6 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hL : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hR : 2 * (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 6 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  exact ⟨fun _ => hR, fun _ => hL⟩
