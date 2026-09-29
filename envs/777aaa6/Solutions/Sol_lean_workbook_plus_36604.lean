-- Prove2me | solution 1 for lean_workbook_plus_36604
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:27.787843+00:00
-- url     : https://prove2.me/submissions/75436467-72b6-4d8c-be96-4d1b8abaca34

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^4 + x^2 - 4 * x + 4 = (x^2 + 1)^2 - (x + 2)^2 + 7 := by
  (intros; linarith)
