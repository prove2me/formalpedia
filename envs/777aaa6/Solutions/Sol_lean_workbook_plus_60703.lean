-- Prove2me | solution 1 for lean_workbook_plus_60703
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:19.534714+00:00
-- url     : https://prove2.me/submissions/ae5a94d4-5f3b-4cba-b65c-6a059d214e41

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y : ℚ) (h : y = 2015 / 2016) : y = 2015 / 2016 := by
  (intros; simp_all)
