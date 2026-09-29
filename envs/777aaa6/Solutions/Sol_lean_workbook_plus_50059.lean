-- Prove2me | solution 1 for lean_workbook_plus_50059
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:08.340735+00:00
-- url     : https://prove2.me/submissions/21d9523d-f0bb-40eb-bd39-e7921c1d14cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 10000 ≠ 0) : 10000 / 2 = 5000 := by
  norm_num
