-- Prove2me | solution 1 for lean_workbook_plus_263
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:36.30771+00:00
-- url     : https://prove2.me/submissions/3ca31002-4e8d-44c0-9046-f4178777a828

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  Int.floor ((13 : ℝ) / 6)^2 = 4 := by
  norm_num
