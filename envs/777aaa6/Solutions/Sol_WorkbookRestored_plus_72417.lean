-- Prove2me | solution 1 for WorkbookRestored.plus_72417
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:23.558977+00:00
-- url     : https://prove2.me/submissions/2989437d-469d-457a-9d43-1f994b73b563

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_72417.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :  Real.cos (2 * π / 7) + Real.cos (4 * π / 7) + Real.cos (6 * π / 7) = - (Real.cos (π / 7) + Real.cos (3 * π / 7) + Real.cos (5 * π / 7))   := by
  rw [← neg_neg (cos (2 * π / 7) + cos (4 * π / 7) + cos (6 * π / 7))]
  rw [← neg_eq_iff_eq_neg]
  simp [cos_add, cos_sub]
  rw [← cos_pi_sub, ← cos_pi_sub, ← cos_pi_sub]
  ring_nf
#print axioms solution
