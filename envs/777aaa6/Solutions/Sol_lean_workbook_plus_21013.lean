-- Prove2me | solution 1 for lean_workbook_plus_21013
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:39.241286+00:00
-- url     : https://prove2.me/submissions/6acac0c7-778e-40b1-949f-1042b92c956e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : a = 0.25 ↔ a = 25 / 100 := by
  norm_num
