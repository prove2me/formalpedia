-- Prove2me | solution 1 for WorkbookRestored.plus_17577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:26.239468+00:00
-- url     : https://prove2.me/submissions/2f1ddf63-c5dc-46d6-adc8-ebfbb2a61e94

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_17577.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, x^2 + 6 = (x * cos x - 3 * sin x) * (x * cos x - 2 * sin x) - (x * sin x + 3 * cos x) * (-x * sin x - 2 * cos x)   := by
  refine' fun x => Eq.symm _
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
