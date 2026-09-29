-- Prove2me | solution 1 for lean_workbook_plus_7986
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:33:55.23958+00:00
-- url     : https://prove2.me/submissions/3bc12361-0f8d-4d2a-810d-c667b01afdf8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 1 / 3 * (1 / 7 + 3 / 14 + 5 / 21) = 5 / 12) : 1 / 3 * (1 / 7 + 3 / 14 + 5 / 21) = 5 / 12 := by
  norm_num
