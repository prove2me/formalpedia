-- Prove2me | solution 1 for WorkbookRestored.plus_5165
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:31:07.482204+00:00
-- url     : https://prove2.me/submissions/8f293ba0-6c1f-4b9e-8df2-0d10bdf6a3d0

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_5165.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ θ : ℝ, tan (θ / 2) ^ 2 = (1 - cos θ) / (1 + cos θ)   := by
  intro θ
  have hc : cos θ = 2 * cos (θ/2)^2 - 1 := by
    have ht := cos_two_mul (θ/2)
    convert ht using 1 <;> congr 1 <;> ring
  rw [tan_eq_sin_div_cos, hc, div_pow]
  have hs : sin (θ/2)^2 = 1 - cos (θ/2)^2 := by
    linarith [sin_sq_add_cos_sq (θ/2)]
  rw [hs]
  by_cases h : cos (θ/2) = 0
  · simp [h]
  · field_simp [h] <;> ring
#print axioms solution
