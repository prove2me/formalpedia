-- Prove2me | solution 1 for WorkbookRestored.plus_631
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:37.602056+00:00
-- url     : https://prove2.me/submissions/383e3b2f-cb0f-4550-9259-d2c9fd6200aa

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_631.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (b A : ℝ) : b^2 - b^2 * Real.sin A * Real.sin A = b^2 * (Real.cos A)^2   := by
  nlinarith [Real.sin_sq_add_cos_sq A]
#print axioms solution
