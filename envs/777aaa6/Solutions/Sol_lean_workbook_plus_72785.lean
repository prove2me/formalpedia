-- Prove2me | solution 1 for lean_workbook_plus_72785
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:03.625467+00:00
-- url     : https://prove2.me/submissions/119579b1-75f1-4629-b0ef-ad59e661aeb3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((1:ℝ) / 42 * (41:ℝ) / 42) * 2 = (41:ℝ) / 882 := by
  norm_num
