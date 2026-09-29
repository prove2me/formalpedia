-- Prove2me | solution 1 for lean_workbook_plus_27774
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:29.278572+00:00
-- url     : https://prove2.me/submissions/dbfc3174-b04b-4fcb-ac21-6533f4782e60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ((1 : ℝ) / 3 * 5 / 2 + 2 / 3 * 4) = 7 / 2 := by
  norm_num
