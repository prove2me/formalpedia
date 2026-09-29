-- Prove2me | solution 1 for WorkbookRestored.plus_21372
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:40.808337+00:00
-- url     : https://prove2.me/submissions/cdc5daa4-6f3b-463d-9705-504759cd9db7

/- Adapted from internlm/Lean-Workbook, Apache-2.0; row lean_workbook_plus_21372.
   Only missing imports/namespaces and the declaration name are repaired. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)   := by
  intros x y
  rw [← Complex.ofReal_inj]
  simp [cos_add, cos_sub, cos_two_mul, sin_two_mul]
  simp [Complex.cos_add_cos, Complex.cos_sub]
#print axioms solution
