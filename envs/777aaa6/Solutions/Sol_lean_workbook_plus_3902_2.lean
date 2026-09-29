-- Prove2me | solution 2 for lean_workbook_plus_3902
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-03-14T02:31:38.078442+00:00
-- url     : https://prove2.me/submissions/8213adb4-cf76-40a9-b2f6-a4e0e6c66499

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (x y : ℝ) :
    x > 2 ∧ y > 2 -> x^2 + x * y + y^2 - 3 * x - 3 * y > 0 := by
  intro hx
  have hx' : x > 2 := by
    exact And.left hx
  have hy' : y > 2 := by
    exact And.right hx
  have hx2 : 0 < x - 2 := by
    linarith
  have hy2 : 0 < y - 2 := by
    linarith
  have hxy : 0 < (x - 2) * (y - 2) := by
    exact mul_pos hx2 hy2
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), hx2, hy2, hxy]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (x y : ℝ) (hx: x > 2 ∧ y > 2) : x^2 + x*y + y^2 - 3*x - 3*y > 0   := by apply solution; repeat assumption
