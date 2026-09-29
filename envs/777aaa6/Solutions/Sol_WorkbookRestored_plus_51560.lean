-- Prove2me | solution 1 for WorkbookRestored.plus_51560
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:45.947025+00:00
-- url     : https://prove2.me/submissions/21f7ef75-890e-43f8-88b6-e2e01bcda560

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51560.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) : (1 - sin θ) * (sin θ ^ 2 + sin θ + 1) = 1 - sin θ ^ 3   := by
  nlinarith [sin_sq_add_cos_sq θ]
#print axioms solution
