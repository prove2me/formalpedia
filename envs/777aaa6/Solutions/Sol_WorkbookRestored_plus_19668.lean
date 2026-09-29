-- Prove2me | solution 1 for WorkbookRestored.plus_19668
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:35.516874+00:00
-- url     : https://prove2.me/submissions/e6ca3caa-2057-41d0-8d82-5e3778280809

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_19668.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)   := by
  exact fun x y ↦ by rw [← Complex.ofReal_inj]; simp [Complex.cos_sub_cos, Complex.sin_sub_sin]
#print axioms solution
