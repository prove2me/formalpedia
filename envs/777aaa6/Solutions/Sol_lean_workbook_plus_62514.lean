-- Prove2me | solution 1 for lean_workbook_plus_62514
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:13.35576+00:00
-- url     : https://prove2.me/submissions/c8bc5543-a0c1-4076-ab93-d17c8aa40c07

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (habc : a * b * c = 1) : (1 / (a ^ 2 - a + 1) ≤ (3 / 2) * (a ^ 2 + 1) / (a ^ 4 + a ^ 2 + 1)) := by
  have hm2 : (0 : ℝ) < 1 + a^2 + (-1)*a := by nlinarith [sq_nonneg (a-1/2)]
  have hm : (0 : ℝ) < 1 + a^2 - a := by nlinarith [sq_nonneg (a-1/2)]
  have hp : (0 : ℝ) < 1 + a + a^2 := by nlinarith [sq_nonneg (a+1/2)]
  intros
  
  have h_identity : (1 + (a ^ 4) + ((-3) * a) + ((-3) * (a ^ 3)) + (4 * (a ^ 2))) = (1 : ℝ) * 1 * ((1 + ((1 / 2) * (a ^ 2)) + ((-3 / 2) * a)))^2 + ((3 / 4) : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (a ^ 4) + ((-3) * a) + ((-3) * (a ^ 3)) + (4 * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * ((1 + (a ^ 2) + ((-1) * a)) ^ 2) * (1 + a + (a ^ 2))) := by positivity
  have h_rational : ((3 / 2) * (a ^ 2 + 1) / (a ^ 4 + a ^ 2 + 1)) - (1 / (a ^ 2 - a + 1)) = ((1 + (a ^ 4) + ((-3) * a) + ((-3) * (a ^ 3)) + (4 * (a ^ 2)))) / ((2 * ((1 + (a ^ 2) + ((-1) * a)) ^ 2) * (1 + a + (a ^ 2)))) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
