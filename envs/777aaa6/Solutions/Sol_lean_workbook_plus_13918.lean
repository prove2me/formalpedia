-- Prove2me | solution 1 for lean_workbook_plus_13918
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:10.812947+00:00
-- url     : https://prove2.me/submissions/c8e221b5-b9d3-45a7-b45b-b4ac1ec2d503

import Mathlib.Analysis.Complex.Basic

theorem solution :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 + b^2 + c^2 + a * b + b * c + c * a ≥ Real.sqrt (2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) * (a + b + c)) := by
  intro a b c ⟨ha, hb, hc⟩
  rw [ge_iff_le, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
