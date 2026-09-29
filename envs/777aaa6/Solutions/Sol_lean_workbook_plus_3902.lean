-- Prove2me | solution 1 for lean_workbook_plus_3902
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-03-14T02:30:36.419128+00:00
-- url     : https://prove2.me/submissions/2adfcb6a-898e-4301-986f-94fe0d375992

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (x y : ℝ) (hx : x > 2 ∧ y > 2) :
    x^2 + x * y + y^2 - 3 * x - 3 * y > 0 := by
  have hx' : x > 2 := hx.1
  have hy' : y > 2 := hx.2
  have hx2 : 0 < x - 2 := by
    linarith
  have hy2 : 0 < y - 2 := by
    linarith
  have hxy : 0 < (x - 2) * (y - 2) := by
    exact mul_pos hx2 hy2
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), hx2, hy2, hxy]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (x y : ℝ) (hx: x > 2 ∧ y > 2) : x^2 + x*y + y^2 - 3*x - 3*y > 0   := by apply solution; repeat assumption
