-- Prove2me | solution 1 for lean_workbook_plus_61175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:58.132875+00:00
-- url     : https://prove2.me/submissions/08f97cea-e6da-4c7a-948c-40040032cb77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = 3.999) : ∃ y, y = ⌊x⌋ := by
  norm_num
