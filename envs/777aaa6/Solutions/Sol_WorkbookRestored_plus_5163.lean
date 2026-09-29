-- Prove2me | solution 1 for WorkbookRestored.plus_5163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:06.734345+00:00
-- url     : https://prove2.me/submissions/ea3fc0fd-43bb-4be1-bb3f-6f8d658e1b11

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5163.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, sin x * cos x ≤ 1 / 2   := by
  refine' fun x => _
  nlinarith [sq_nonneg (sin x - cos x), sin_sq_add_cos_sq x]
#print axioms solution
