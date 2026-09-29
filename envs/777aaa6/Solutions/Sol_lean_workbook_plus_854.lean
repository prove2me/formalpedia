-- Prove2me | solution 1 for lean_workbook_plus_854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:46.922115+00:00
-- url     : https://prove2.me/submissions/55ebf486-ba55-4eb5-8aa6-77981c6aaac9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x k z : ℝ) : ∃ x1 k1 z1 : ℝ, x1 = x / 3 ∧ k1 = k / 3 ∧ z1 = z / 3 := by
  norm_num
