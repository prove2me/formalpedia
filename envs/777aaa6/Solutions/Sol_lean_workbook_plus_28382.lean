-- Prove2me | solution 1 for lean_workbook_plus_28382
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:45.308733+00:00
-- url     : https://prove2.me/submissions/4d62b447-1028-499f-91fb-d679f4656e01

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^4 + x^2 + 1 = (x^2 - x + 1) * (x^2 + x + 1) := by
  (intros; linarith)
