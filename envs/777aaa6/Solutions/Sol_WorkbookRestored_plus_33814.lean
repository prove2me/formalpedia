-- Prove2me | solution 1 for WorkbookRestored.plus_33814
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:45.446983+00:00
-- url     : https://prove2.me/submissions/92ae2273-9997-498a-8811-07f2413fc159

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33814.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (A B : ℝ) : Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B   := by
  simp [sub_eq_add_neg, cos_add, cos_neg, sin_neg]
#print axioms solution
