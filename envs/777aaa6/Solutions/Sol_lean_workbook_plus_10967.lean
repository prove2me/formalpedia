-- Prove2me | solution 1 for lean_workbook_plus_10967
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:32.428991+00:00
-- url     : https://prove2.me/submissions/ac868cf9-1b57-4235-b1c1-80ebfb4d0e93

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x = y ∧ y = z ∧ z = 1 / 3 ↔ x = y ∧ y = z ∧ z = 1 / 3 := by
  norm_num
