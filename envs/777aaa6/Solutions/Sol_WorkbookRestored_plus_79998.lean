-- Prove2me | solution 1 for WorkbookRestored.plus_79998
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:32.786125+00:00
-- url     : https://prove2.me/submissions/18a994f2-462e-4916-a879-b00c2d26e869

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_79998.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (sin x)^4 = 3/8 - 4/8 * cos (2 * x) + 1/8 * cos (4 * x)   := by
  rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, cos_two_mul]
  simp [cos_two_mul, sin_sq]
  nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
