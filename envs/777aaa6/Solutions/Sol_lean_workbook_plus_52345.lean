-- Prove2me | solution 1 for lean_workbook_plus_52345
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:43.673839+00:00
-- url     : https://prove2.me/submissions/5dec722a-1b58-43cc-8eec-8cb811f0f769

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : (2014^4 + 4 * 2013^4) / (2013^2 + 4027^2) - (2012^4 + 4 * 2013^4) / (2013^2 + 4025^2) = 0 := by
  norm_num
