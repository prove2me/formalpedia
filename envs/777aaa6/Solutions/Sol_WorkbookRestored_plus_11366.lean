-- Prove2me | solution 1 for WorkbookRestored.plus_11366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:02.61598+00:00
-- url     : https://prove2.me/submissions/32c625a0-63f6-43bc-9b04-bf92f2fd45ab

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_11366.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2) :
  Real.sin x + Real.cos x ≤ Real.sqrt 2   := by
  have h₁ : 0 ≤ (Real.cos x - Real.sin x)^2 := sq_nonneg _
  apply le_sqrt_of_sq_le
  nlinarith [Real.sin_sq_add_cos_sq x]
#print axioms solution
