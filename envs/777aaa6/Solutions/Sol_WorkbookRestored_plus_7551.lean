-- Prove2me | solution 1 for WorkbookRestored.plus_7551
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:12.922554+00:00
-- url     : https://prove2.me/submissions/02ef204c-1512-4e1d-9e9d-0f5bb96f19d4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_7551.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (sin x)^4 + (cos x)^4 = 2 * (cos x)^4 + 1 - 2 * (cos x)^2   := by
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
