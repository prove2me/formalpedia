-- Prove2me | solution 1 for lean_workbook_plus_37022
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:17.652372+00:00
-- url     : https://prove2.me/submissions/904444d6-8e70-460e-8014-3d66bdf8d78d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : a ≠ 0) (ha' : a ≠ -1) : ∃ x y z : ℝ, x = a ∧ y = -1/(a+1) ∧ z = -(a+1)/a := by
  norm_num
