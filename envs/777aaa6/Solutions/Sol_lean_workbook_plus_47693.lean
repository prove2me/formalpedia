-- Prove2me | solution 1 for lean_workbook_plus_47693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:17.609599+00:00
-- url     : https://prove2.me/submissions/2197bc91-a5db-40cd-8b52-02a66c387352

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) (ha : a^2 ≤ 1) : (3 * a^2 - 1) / ((3 - 2 * a^2) * (a^2 + 2)) ≥ (27 * a^2 - 9) / 49 := by
  intros
  have hp : (0 : ℝ) < 3 - 2*a^2 := by nlinarith
  
  have h_identity : (5 + ((-24) * (a ^ 2)) + (9 * (a ^ 4)) + (54 * (a ^ 6))) = (5 : ℝ) * 1 * ((1 + ((-3) * (a ^ 2))))^2 + (6 : ℝ) * 1 * ((a + ((-3) * (a ^ 3))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (5 + ((-24) * (a ^ 2)) + (9 * (a ^ 4)) + (54 * (a ^ 6))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-49) * ((-3) + (2 * (a ^ 2))) * (2 + (a ^ 2))) := by
    convert mul_pos (mul_pos (show (0:ℝ)<49 by norm_num) hp) (show (0:ℝ)<2+a^2 by positivity) using 1 <;> ring
  have h_rational : ((3 * a^2 - 1) / ((3 - 2 * a^2) * (a^2 + 2))) - ((27 * a^2 - 9) / 49) = ((5 + ((-24) * (a ^ 2)) + (9 * (a ^ 4)) + (54 * (a ^ 6)))) / (((-49) * ((-3) + (2 * (a ^ 2))) * (2 + (a ^ 2)))) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
