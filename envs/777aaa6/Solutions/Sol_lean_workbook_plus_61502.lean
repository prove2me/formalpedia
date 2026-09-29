-- Prove2me | solution 1 for lean_workbook_plus_61502
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:45.13731+00:00
-- url     : https://prove2.me/submissions/b44fd1eb-7a95-4391-973b-b090015df7ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : (1 + a) / 2 - (1 - a) / 2 = a := by
  (intros; linarith)
