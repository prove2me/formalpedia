-- Prove2me | solution 1 for WorkbookRestored.plus_27452
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:57.298349+00:00
-- url     : https://prove2.me/submissions/1280678d-4d98-41f5-8fc0-a4c32ae12cfa

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_27452.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : Real.sin (3*x) = (1 + 2*Real.cos (2*x))*Real.sin x   := by
  simp [sin_three_mul, cos_two_mul, sin_two_mul, cos_sq']
  ring
#print axioms solution
