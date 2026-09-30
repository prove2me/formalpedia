-- Prove2me | solution 1 for lean_workbook_plus_12743
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:51.975637+00:00
-- url     : https://prove2.me/submissions/32e6b851-71b8-483a-af2b-0401dc86203e

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, 2 * (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
