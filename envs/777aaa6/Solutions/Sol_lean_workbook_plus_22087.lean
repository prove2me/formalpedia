-- Prove2me | solution 1 for lean_workbook_plus_22087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:34.195126+00:00
-- url     : https://prove2.me/submissions/1072eab8-79f0-4942-a8a5-521a4372db70

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x) : x + 1 / (x + 1) ≥ 3 / 4 * (x + 1) := by
  intros
  
  have h_identity : (1 + (x ^ 2) + ((-2) * x)) = (1 : ℝ) * 1 * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 2) + ((-2) * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * (1 + x)) := by positivity
  have h_rational : (x + 1 / (x + 1)) - (3 / 4 * (x + 1)) = ((1 + (x ^ 2) + ((-2) * x))) / ((4 * (1 + x))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
