-- Prove2me | solution 1 for WorkbookRestored.plus_34171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:47.482434+00:00
-- url     : https://prove2.me/submissions/d156d448-dbb9-4dd9-9924-a30bfcd64d15

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34171.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ C : ℝ, sin C * (1 - sin C) ≤ 1 / 4   := by
  exact fun C ↦ by nlinarith [sq_nonneg (sin C - 1/2)]
#print axioms solution
