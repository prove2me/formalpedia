-- Prove2me | solution 1 for lean_workbook_plus_36273
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:51.704043+00:00
-- url     : https://prove2.me/submissions/cdae5299-891d-4dab-ab26-9e4ec75e6479

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (2 : ℝ) < 3 → Real.sqrt 2 < Real.sqrt 3 := by
  norm_num
