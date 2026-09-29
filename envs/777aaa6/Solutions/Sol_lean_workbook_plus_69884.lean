-- Prove2me | solution 1 for lean_workbook_plus_69884
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:14.660607+00:00
-- url     : https://prove2.me/submissions/154be974-a542-440a-bba0-a83aa33c8707

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (-2 < x ∧ x < 2 ∧ y < x^2 / 4 ∧ y > x - 1 ∧ y > -x + 1) ↔ -2 < x ∧ x < 2 ∧ y < x^2 / 4 ∧ y > x - 1 ∧ y > -x + 1 := by
  norm_num
