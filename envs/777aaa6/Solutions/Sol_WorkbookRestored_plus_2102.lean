-- Prove2me | solution 1 for WorkbookRestored.plus_2102
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:29:18.131068+00:00
-- url     : https://prove2.me/submissions/5775a0c9-8338-47e7-905c-4b595534fa2b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_2102.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) : sin (2 * θ) = 2 * tan θ / (1 + tan θ ^ 2)   := by
  rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  by_cases hc : cos θ = 0
  · simp [hc]
  · have hd : 1 + (sin θ / cos θ)^2 = 1 / (cos θ)^2 := by
      field_simp [hc]
      nlinarith [sin_sq_add_cos_sq θ]
    rw [hd]
    field_simp [hc] <;> ring
#print axioms solution
