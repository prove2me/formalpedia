-- Prove2me | solution 1 for lean_workbook_plus_14597
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:48.650506+00:00
-- url     : https://prove2.me/submissions/8ee7d7ed-231a-4d57-8c21-ff423c5f82b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b = 0) : b * a = 0 := by
  (intros; linarith)
