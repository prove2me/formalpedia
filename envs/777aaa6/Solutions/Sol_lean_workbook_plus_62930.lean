-- Prove2me | solution 1 for lean_workbook_plus_62930
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:58.188078+00:00
-- url     : https://prove2.me/submissions/73769469-b7c3-4703-ba71-647e6269d361

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ⌊(1.5 : ℝ)⌋ = 1 := by
  norm_num
