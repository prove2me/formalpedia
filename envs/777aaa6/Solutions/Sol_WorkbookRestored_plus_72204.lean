-- Prove2me | solution 1 for WorkbookRestored.plus_72204
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:22.808975+00:00
-- url     : https://prove2.me/submissions/a3c8bc1c-16e5-46ea-a957-a64ed40c3416

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_72204.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (t : ℝ) : Real.cosh (3 * t) = Real.cosh t * (4 * (Real.cosh t)^2 - 3)   := by
  rw [← mul_right_inj' (cosh_pos t).ne', cosh_three_mul]
  ring
#print axioms solution
