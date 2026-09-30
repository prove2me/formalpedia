-- Prove2me | solution 2 for lean_workbook_plus_1577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:23.168562+00:00
-- url     : https://prove2.me/submissions/fcd0a1d9-0fe0-4cef-be27-a95bc53f07d8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (z : ℝ) (hz : -1/3 ≤ z) : z / (z^2 + 1) ≤ 1/2 := by
  intros
  
  have h_identity : (1 + (z ^ 2) + ((-2) * z)) = (1 : ℝ) * 1 * ((1 + ((-1) * z)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (z ^ 2) + ((-2) * z)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (1 + (z ^ 2))) := by positivity
  have h_rational : (1/2) - (z / (z^2 + 1)) = ((1 + (z ^ 2) + ((-2) * z))) / ((2 * (1 + (z ^ 2)))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
