-- Prove2me | solution 1 for lean_workbook_plus_21011
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:41.714991+00:00
-- url     : https://prove2.me/submissions/b1a559c4-930f-4d70-a486-43f9ceb990bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (2014^4 + 4 * 2013^4) / (2013^2 + 4027^2) - (2012^4 + 4 * 2013^4) / (2013^2 + 4025^2) = 0 := by
  norm_num
