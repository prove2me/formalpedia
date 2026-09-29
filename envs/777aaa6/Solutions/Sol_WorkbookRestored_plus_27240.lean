-- Prove2me | solution 1 for WorkbookRestored.plus_27240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:56.516613+00:00
-- url     : https://prove2.me/submissions/3409699b-0efa-49cb-8430-bf29563e53c4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_27240.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 1 / Real.tan 1 = Real.cos 1 / Real.sin 1   := by
  simp [tan_eq_sin_div_cos, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
#print axioms solution
