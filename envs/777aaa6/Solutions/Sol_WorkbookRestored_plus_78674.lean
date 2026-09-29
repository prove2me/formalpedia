-- Prove2me | solution 1 for WorkbookRestored.plus_78674
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:30.758953+00:00
-- url     : https://prove2.me/submissions/324e469b-d4fa-427a-be51-76eacfbe3385

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_78674.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : sin x - sin y = 2 * cos ((x + y) / 2) * sin ((x - y) / 2)   := by
  rw [← Complex.ofReal_inj]
  simp [Complex.sin_sub_sin, Complex.cos_add, Complex.cos_sub, mul_comm, mul_assoc, mul_left_comm]
#print axioms solution
