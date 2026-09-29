-- Prove2me | solution 1 for WorkbookRestored.plus_21175
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:39.821983+00:00
-- url     : https://prove2.me/submissions/cf731666-a422-4599-bc30-700890639e5c

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_21175.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (α β : ℝ) : sin α ^ 2 * cos β ^ 2 - cos α ^ 2 * sin β ^ 2 = sin α ^ 2 - sin β ^ 2   := by
  simp [sin_sq, cos_sq, sub_mul, mul_sub, mul_assoc, mul_comm, mul_left_comm]
#print axioms solution
