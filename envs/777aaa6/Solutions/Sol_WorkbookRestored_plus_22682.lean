-- Prove2me | solution 1 for WorkbookRestored.plus_22682
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:43.311729+00:00
-- url     : https://prove2.me/submissions/30315c0c-182c-469d-9d52-3816d164108f

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_22682.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, Real.cos (8 * x) = 1 - 32 * (Real.sin x)^2 + 160 * (Real.sin x)^4 - 256 * (Real.sin x)^6 + 128 * (Real.sin x)^8   := by
  intro x
  rw [show (8 : ℝ)*x = 2*(2*(2*x)) by ring, cos_two_mul, cos_two_mul, cos_two_mul, cos_sq']
  ring
#print axioms solution
