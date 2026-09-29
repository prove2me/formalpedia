-- Prove2me | solution 1 for lean_workbook_plus_47997
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:52.673771+00:00
-- url     : https://prove2.me/submissions/134b6179-aef1-429a-bfcc-c7138ce380f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 7*a + 2.5*b + 0*c = 7*a + 2.5*b := by
  norm_num
