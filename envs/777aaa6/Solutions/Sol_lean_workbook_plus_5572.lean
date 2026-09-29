-- Prove2me | solution 1 for lean_workbook_plus_5572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:44.585949+00:00
-- url     : https://prove2.me/submissions/be799069-b3f4-4efa-9f6e-dfcf0bc9ee0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  1 - (1000 : ℝ) / 2001 = 1001 / 2001 := by
  norm_num
