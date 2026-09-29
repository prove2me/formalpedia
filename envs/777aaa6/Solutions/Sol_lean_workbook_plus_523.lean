-- Prove2me | solution 1 for lean_workbook_plus_523
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:12.820423+00:00
-- url     : https://prove2.me/submissions/8a974c15-b60c-4aad-bb08-0138f2650213

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ x : ℝ, x ≠ 1 → (x^2 + x + 1) / (x - 1) ^ 2 ≥ 1 / 4 := by
  intro x hx
  have hxm : (-1:ℝ) + x ≠ 0 := by intro he; apply hx; linarith
  have hp : (0 : ℝ) < (x-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  
  have h_identity : (3 + (3 * (x ^ 2)) + (6 * x)) = (3 : ℝ) * 1 * ((1 + x))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (3 + (3 * (x ^ 2)) + (6 * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * (((-1) + x) ^ 2)) := by positivity
  have h_rational : ((x^2 + x + 1) / (x - 1) ^ 2) - (1 / 4) = ((3 + (3 * (x ^ 2)) + (6 * x))) / ((4 * (((-1) + x) ^ 2))) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
