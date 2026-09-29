-- Prove2me | solution 1 for lean_workbook_plus_26988
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:23.551453+00:00
-- url     : https://prove2.me/submissions/bac367fd-6235-49ec-a12a-cf11eba64e36

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 0 < 2017) : 2017 - (2017 / 3) = 1345 := by
  norm_num
