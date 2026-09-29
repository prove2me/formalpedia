-- Prove2me | solution 1 for lean_workbook_plus_60872
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:37.179827+00:00
-- url     : https://prove2.me/submissions/1dfaf981-7e63-4c1a-82ae-1af79aa113eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 3 * x - 5 < 7 → x < 4 := by
  (intros; linarith)
