-- Prove2me | solution 1 for lean_workbook_plus_54497
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:05.281031+00:00
-- url     : https://prove2.me/submissions/9f82c252-2344-4851-9cb2-67886a6dce5f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > 0) : x = x := by
  norm_num
