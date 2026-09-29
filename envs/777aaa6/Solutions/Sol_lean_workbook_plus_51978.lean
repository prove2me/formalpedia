-- Prove2me | solution 1 for lean_workbook_plus_51978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:17.742153+00:00
-- url     : https://prove2.me/submissions/33036968-1655-4898-9409-8e6458312ddc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : a > 0) (hb : b > 0) : (2 * a + b) ^ 2 / b + 81 * a ^ 2 * b / (2 * a + b) ^ 2 ≥ 18 * a := by
  intros
  
  have h_identity : ((b ^ 4) + (16 * (a ^ 4)) + ((-40) * b * (a ^ 3)) + ((-10) * a * (b ^ 3)) + (33 * (a ^ 2) * (b ^ 2))) = (16 : ℝ) * 1 * (((a ^ 2) + ((1 / 4) * (b ^ 2)) + ((-5 / 4) * a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((b ^ 4) + (16 * (a ^ 4)) + ((-40) * b * (a ^ 3)) + ((-10) * a * (b ^ 3)) + (33 * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (b * ((b + (2 * a)) ^ 2)) := by positivity
  have h_rational : ((2 * a + b) ^ 2 / b + 81 * a ^ 2 * b / (2 * a + b) ^ 2) - (18 * a) = (((b ^ 4) + (16 * (a ^ 4)) + ((-40) * b * (a ^ 3)) + ((-10) * a * (b ^ 3)) + (33 * (a ^ 2) * (b ^ 2)))) / ((b * ((b + (2 * a)) ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
