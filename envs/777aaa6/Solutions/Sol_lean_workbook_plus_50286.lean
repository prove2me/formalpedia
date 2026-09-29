-- Prove2me | solution 1 for lean_workbook_plus_50286
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:04.100259+00:00
-- url     : https://prove2.me/submissions/dc415171-1c12-49cd-916a-30cbca4c4ff5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 31 * 2 + 4 + 5 = 71) : 31 * 2 + 4 + 5 = 71 := by
  norm_num
