-- Prove2me | solution 1 for lean_workbook_plus_77183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:50.81394+00:00
-- url     : https://prove2.me/submissions/dbd53eef-c329-4a7c-a460-c7305935f87d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a : ℝ) (h₀ : a ^ 2 = 4) : a = 2 ∨ a = -2 := by
  have hfac : (a - 2) * (a + 2) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · left
    linarith
  · right
    linarith
