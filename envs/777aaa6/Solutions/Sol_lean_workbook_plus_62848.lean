-- Prove2me | solution 1 for lean_workbook_plus_62848
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:15.299983+00:00
-- url     : https://prove2.me/submissions/f1a2f2b2-eaf2-4b67-affe-4f15c4966bda

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (27:ℝ) / 4 + 64 / 27 ≥ 985 / 108 := by
  norm_num
