-- Prove2me | solution 1 for lean_workbook_plus_27625
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:33.745279+00:00
-- url     : https://prove2.me/submissions/e2dcf0be-98ac-406d-8899-cced731a5ba0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℚ) (h : a = 1 / 8) : (1 / 8) / (2 * (1 / 8) + 1 / 16 + 1 / 32) = 4 / 11 := by
  norm_num
