-- Prove2me | solution 1 for WorkbookRestored.plus_2614
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:20.576559+00:00
-- url     : https://prove2.me/submissions/356147f9-d48b-489f-b7f8-868a2e187154

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2614.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p q α β θ : ℝ) (hp : cos (θ - α) = p) (hq : sin (θ + β) = q) : p^2 + q^2 - 2 * p * q * sin (α + β) = cos (α + β)^2   := by
  simp [hp.symm, hq.symm, cos_add, cos_sub, sin_add, sin_sub]
  nlinarith [cos_sq_add_sin_sq θ, cos_sq_add_sin_sq α, cos_sq_add_sin_sq β]
#print axioms solution
