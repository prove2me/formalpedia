-- Prove2me | solution 1 for lean_workbook_plus_51982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:42.802816+00:00
-- url     : https://prove2.me/submissions/2bebca2b-fb03-4fb1-906c-bc3f583b840e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) : (a^2/(a^2 + 4) + 2/(1 + (a + 1)^2)) ≥ 3/5 := by
  have hp : (0 : ℝ) < 2 + a^2 + 2*a := by nlinarith [sq_nonneg (a+1)]
  intros
  
  have h_identity : (16 + ((-24) * a) + (2 * (a ^ 2)) + (2 * (a ^ 4)) + (4 * (a ^ 3))) = (16 : ℝ) * 1 * ((1 + ((-3 / 4) * a) + ((-1 / 4) * (a ^ 2))))^2 + (1 : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (16 + ((-24) * a) + (2 * (a ^ 2)) + (2 * (a ^ 4)) + (4 * (a ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (5 * (4 + (a ^ 2)) * (2 + (a ^ 2) + (2 * a))) := by positivity
  have h_rational : ((a^2/(a^2 + 4) + 2/(1 + (a + 1)^2))) - (3/5) = ((16 + ((-24) * a) + (2 * (a ^ 2)) + (2 * (a ^ 4)) + (4 * (a ^ 3)))) / ((5 * (4 + (a ^ 2)) * (2 + (a ^ 2) + (2 * a)))) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
