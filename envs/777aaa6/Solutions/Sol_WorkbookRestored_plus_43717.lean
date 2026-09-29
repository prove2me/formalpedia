-- Prove2me | solution 1 for WorkbookRestored.plus_43717
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:07.478022+00:00
-- url     : https://prove2.me/submissions/7b2c4993-327e-4942-b223-f0c643f71026

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_43717.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, (exp x / (4 + 5 * exp (3 * x))) * (exp (-x) / exp (-x)) = 1 / (4 * exp (-x) + 5 * exp (2 * x))   := by
  intro x
  field_simp [exp_ne_zero]
  ring_nf
  simp [← exp_add, ← exp_mul]
  ring
#print axioms solution
