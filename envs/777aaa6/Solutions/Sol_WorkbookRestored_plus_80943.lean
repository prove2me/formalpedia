-- Prove2me | solution 1 for WorkbookRestored.plus_80943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:37.574238+00:00
-- url     : https://prove2.me/submissions/4095dec2-0b7c-4484-9d0e-c681f2a450da

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80943.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c : ℝ) :
  Real.sin (a + b - 2 * c) * Real.cos b - Real.sin (a + c - 2 * b) * Real.cos c
  = Real.sin (b - c) * (Real.cos (b + c - a) + Real.cos (a + c - b) + Real.cos (a + b - c))   := by
  simp only [sin_add, sin_sub, cos_add, cos_sub, sin_two_mul, cos_two_mul]
  linear_combination (-cos a * cos c * sin c - cos c^2 * sin a) * (sin_sq_add_cos_sq b)
    + (cos a * cos b * sin b + cos b^2 * sin a) * (sin_sq_add_cos_sq c)
#print axioms solution
