-- Prove2me | solution 1 for lean_workbook_plus_54491
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:50.257415+00:00
-- url     : https://prove2.me/submissions/33e48398-5d98-41a6-a181-091912032a21

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ⌈(14 : ℝ) / 3⌉ = 5 := by
  norm_num
