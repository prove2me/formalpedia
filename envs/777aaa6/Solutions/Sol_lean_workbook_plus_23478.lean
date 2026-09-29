-- Prove2me | solution 1 for lean_workbook_plus_23478
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:10.988296+00:00
-- url     : https://prove2.me/submissions/30c7bb67-d4dc-41c5-88bd-9fd44da39d5b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 6 * x + 1 / 4 * x^2 - 1 / 4 * x = 72) :
  x^2 + 23 * x - 288 = 0 := by
  (intros; linarith)
