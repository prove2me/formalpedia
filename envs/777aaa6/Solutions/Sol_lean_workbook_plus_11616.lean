-- Prove2me | solution 1 for lean_workbook_plus_11616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:17:24.582081+00:00
-- url     : https://prove2.me/submissions/9f4c2739-8dc5-4294-8e2b-691ce7056ccb

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b : ℝ, a > 0 ∧ b > 0 ∧ a^2 + b^3 ≥ a^3 + b^4 → a^3 + b^3 ≤ 2 := by
  rintro a b ⟨ha, hb, hab⟩
  have h1 : 0 ≤ (a - 1) ^ 2 * (1 + 2 * a) := mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ (b - 1) ^ 2 * (3 * b ^ 2 + 2 * b + 1) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith [h1, h2, hab]
