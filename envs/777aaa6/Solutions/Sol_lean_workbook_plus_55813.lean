-- Prove2me | solution 1 for lean_workbook_plus_55813
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:21:53.893494+00:00
-- url     : https://prove2.me/submissions/bb718997-d349-4f81-8698-e08c33f8bcf8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  x^4 - 4 * x^3 + 8 * x + 4 = (x^2 - 2 * x - 2)^2 := by
  (intros; linarith)
