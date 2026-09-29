-- Prove2me | solution 1 for lean_workbook_plus_50613
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:12.130672+00:00
-- url     : https://prove2.me/submissions/c6c372c4-e5da-4d20-8c54-9eaae9b1af60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : (a * b + 1)^2 = (2 * a + 2 * b)^2) :
  (a * b + 1 + 2 * a + 2 * b) * (a * b + 1 - 2 * a - 2 * b) = 0 := by
  (intros; linarith)
