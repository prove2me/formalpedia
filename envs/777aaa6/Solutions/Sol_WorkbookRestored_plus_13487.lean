-- Prove2me | solution 1 for WorkbookRestored.plus_13487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:10.125327+00:00
-- url     : https://prove2.me/submissions/3b2ebdeb-c872-49be-a39d-330ee2de174b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_13487.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ x : ℝ, 1 / 4 ≤ cos x ^ 6 + sin x ^ 6 ∧ cos x ^ 6 + sin x ^ 6 ≤ 1   := by
  intro x
  have h1 : 0 ≤ (cos x ^ 2 - sin x ^ 2) ^ 2 := sq_nonneg _
  have h2 := sq_nonneg (cos x ^ 2 + sin x ^ 2)
  constructor <;> nlinarith [cos_sq_add_sin_sq x]
#print axioms solution
