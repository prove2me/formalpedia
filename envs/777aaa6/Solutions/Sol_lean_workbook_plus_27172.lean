-- Prove2me | solution 1 for lean_workbook_plus_27172
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:58.444746+00:00
-- url     : https://prove2.me/submissions/85c7c3dc-2c32-4c24-876e-c6f59dc74ea8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a = 1) (hb : b = 1) (hc : c = 1) : (a^(1/2) + 2 * b^(1/3) + 3 * c^(1/5))^2018 = 6^2018 := by
  norm_num
