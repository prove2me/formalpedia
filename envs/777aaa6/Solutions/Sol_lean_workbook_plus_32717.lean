-- Prove2me | solution 1 for lean_workbook_plus_32717
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:20.705858+00:00
-- url     : https://prove2.me/submissions/bc456357-068a-4809-a8f5-83992ead9bd7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^8 + 14 * x^4 + 1 = (x^2 + 1)^4 - (2 * x^3 - 2 * x)^2 := by
  (intros; linarith)
