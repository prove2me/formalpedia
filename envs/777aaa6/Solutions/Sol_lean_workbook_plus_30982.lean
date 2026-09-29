-- Prove2me | solution 1 for lean_workbook_plus_30982
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:12.858179+00:00
-- url     : https://prove2.me/submissions/2c379044-1152-460c-89ed-470da167d353

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B C : ℝ) : (A / 3 + B - C) / 2 = 0 ↔ A / 3 + B - C = 0 := by
  norm_num
