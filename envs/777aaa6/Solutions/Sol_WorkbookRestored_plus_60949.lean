-- Prove2me | solution 1 for WorkbookRestored.plus_60949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:08.520532+00:00
-- url     : https://prove2.me/submissions/b064d4d1-7d21-4123-a379-8537785c2e12

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_60949.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) : abs (sin x) + abs (cos x) ≥ 1   := by
  cases le_total 0 (sin x) <;> cases le_total 0 (cos x) <;> simp [abs_of_nonneg, abs_of_nonpos, *] <;> nlinarith [sin_sq_add_cos_sq x]
#print axioms solution
