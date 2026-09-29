-- Prove2me | solution 1 for lean_workbook_plus_17900
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:56.360009+00:00
-- url     : https://prove2.me/submissions/21bdd6cd-c41a-4924-ba65-cdab80185d83

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℝ) : y^2 + y^2 / 3 = 4 * y^2 / 3 := by
  (intros; linarith)
