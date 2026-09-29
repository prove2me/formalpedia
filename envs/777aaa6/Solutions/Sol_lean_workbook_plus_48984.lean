-- Prove2me | solution 1 for lean_workbook_plus_48984
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:20.17476+00:00
-- url     : https://prove2.me/submissions/8aec1016-20c6-4c7b-9ce8-d17361749e9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 12 * 3 + 4 * 5 = 56) : 12 * 3 + 4 * 5 = 56 := by
  norm_num
