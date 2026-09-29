-- Prove2me | solution 1 for lean_workbook_plus_71850
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:55.97742+00:00
-- url     : https://prove2.me/submissions/9d958948-8299-43ec-815e-016f082134f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : a ≠ 0) (ha' : a ≠ -1) : ∃ x y z : ℝ, x = -1/(a+1) ∧ y = -(a+1)/a ∧ z = a := by
  norm_num
