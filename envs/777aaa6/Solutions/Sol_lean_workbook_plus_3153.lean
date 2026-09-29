-- Prove2me | solution 1 for lean_workbook_plus_3153
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:24.806082+00:00
-- url     : https://prove2.me/submissions/f308724d-da95-47d0-aef9-7fb4a5b83ed1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x) : (2 * x / (x ^ 2 + 4) + 1 / (3 * x ^ 2 + 2)) ≤ 3 / 5 := by
  intros
  
  have h_identity : (4 + ((-30) * (x ^ 3)) + ((-20) * x) + (9 * (x ^ 4)) + (37 * (x ^ 2))) = (4 : ℝ) * 1 * ((1 + ((-5 / 2) * x) + ((3 / 2) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (4 + ((-30) * (x ^ 3)) + ((-20) * x) + (9 * (x ^ 4)) + (37 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (5 * (2 + (3 * (x ^ 2))) * (4 + (x ^ 2))) := by positivity
  have h_rational : (3 / 5) - ((2 * x / (x ^ 2 + 4) + 1 / (3 * x ^ 2 + 2))) = ((4 + ((-30) * (x ^ 3)) + ((-20) * x) + (9 * (x ^ 4)) + (37 * (x ^ 2)))) / ((5 * (2 + (3 * (x ^ 2))) * (4 + (x ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
