-- Prove2me | solution 1 for lean_workbook_plus_20673
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:49.342324+00:00
-- url     : https://prove2.me/submissions/d9a4bbe2-b588-409b-ac37-f304a0ad71f7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  (33600 : ℝ) / (56 * 60) = 10 := by
  norm_num
