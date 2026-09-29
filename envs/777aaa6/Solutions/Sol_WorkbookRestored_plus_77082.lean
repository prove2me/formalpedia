-- Prove2me | solution 1 for WorkbookRestored.plus_77082
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:28.506984+00:00
-- url     : https://prove2.me/submissions/521499c9-def6-4de1-937f-281108ec5de7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_77082.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ)
  (h₀ : cos x ≠ 0) :
  sin (2 * x) / cos x = 2 * sin x   := by
  simp [sin_two_mul, h₀]
#print axioms solution
