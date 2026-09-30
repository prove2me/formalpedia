-- Prove2me | solution 1 for lean_workbook_plus_11878
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:25.933173+00:00
-- url     : https://prove2.me/submissions/3cd4af95-12f9-4593-9b5c-f50e54eee031

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x : ℝ, 1 < x → 2 * x ^ 4 - x ^ 3 + x ^ 2 - x - 1 > 0 := by
  intro x hx
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < 2 * x ^ 3 + x ^ 2 + 2 * x + 1 := by positivity
  nlinarith [mul_pos h1 h2]
