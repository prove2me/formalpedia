-- Prove2me | solution 1 for WorkbookRestored.plus_26146
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:51.855979+00:00
-- url     : https://prove2.me/submissions/2fc0b83d-82d9-478c-a8cb-f8d769040b7f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_26146.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℝ, |cos x * sin x| ≤ 1 / 2   := by
  intro x
  have := sq_nonneg (Real.cos x - Real.sin x)
  have := sq_nonneg (Real.cos x + Real.sin x)
  exact (abs_le.2 ⟨by nlinarith [Real.sin_sq_add_cos_sq x], by nlinarith [Real.sin_sq_add_cos_sq x]⟩)
#print axioms solution
