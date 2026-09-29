-- Prove2me | solution 1 for WorkbookRestored.plus_36620
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:52.432685+00:00
-- url     : https://prove2.me/submissions/4079dc7b-339a-4a5a-87c8-6d4e4fda3633

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_36620.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) : sin (2 * θ) = 2 / (tan θ + 1 / tan θ)   := by
  rw [sin_two_mul, tan_eq_sin_div_cos]
  by_cases hs : sin θ = 0
  · simp [hs]
  by_cases hc : cos θ = 0
  · simp [hc]
  have hq : sin θ / cos θ + 1 / (sin θ / cos θ) = 1 / (sin θ * cos θ) := by
    field_simp
    nlinarith [sin_sq_add_cos_sq θ]
  rw [hq]
  rw [div_div_eq_mul_div]
  simp only [div_one]
  ring
#print axioms solution
