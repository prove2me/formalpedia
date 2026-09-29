-- Prove2me | solution 1 for WorkbookRestored.plus_17667
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:26.930465+00:00
-- url     : https://prove2.me/submissions/57c5ae8b-d923-4a1c-b600-07b2f0eb8611

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_17667.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x y : ℝ, x > 0 ∧ y > 0 → x^4*y^4 ≥ x^3*y^3 + Real.log (x*y)   := by
  rintro x y ⟨hx, hy⟩
  have h1 : 0 < x * y := mul_pos hx hy
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * y + 1), Real.log_le_sub_one_of_pos h1]
#print axioms solution
