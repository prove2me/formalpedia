-- Prove2me | solution 1 for WorkbookRestored.plus_8402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:14.555679+00:00
-- url     : https://prove2.me/submissions/a9e7e19d-19c6-4638-b108-9850a468d16d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_8402.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : (-1 ≤ cos x ^ 6 - sin x ^ 4 ∧ cos x ^ 6 - sin x ^ 4 ≤ 1)   := by
  have := sq_nonneg (cos x ^ 2 - sin x ^ 2)
  have := sq_nonneg (cos x ^ 2 + sin x ^ 2)
  constructor <;> nlinarith [cos_sq_add_sin_sq x]
#print axioms solution
