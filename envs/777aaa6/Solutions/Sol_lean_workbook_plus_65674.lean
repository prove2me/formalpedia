-- Prove2me | solution 1 for lean_workbook_plus_65674
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:20.001596+00:00
-- url     : https://prove2.me/submissions/2212ff54-7a48-471d-be6d-30a100561523

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^4 + b^4 + (a + b)^4 = 2 * (a^2 + a * b + b^2)^2 := by
  (intros; linarith)
