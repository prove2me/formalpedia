-- Prove2me | solution 1 for lean_workbook_plus_10232
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:04.094525+00:00
-- url     : https://prove2.me/submissions/fc33928a-5620-47cf-8c12-a7aeb0a47ead

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * c / (a + c) + b * d / (b + d)) ≤ (a + b) * (c + d) / (a + b + c + d) := by
  intros
  
  have h_identity : (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) = (1 : ℝ) * 1 * (((a * d) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + c) * (b + d) * (a + b + c + d)) := by positivity
  have h_rational : ((a + b) * (c + d) / (a + b + c + d)) - ((a * c / (a + c) + b * d / (b + d))) = ((((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d))) / (((a + c) * (b + d) * (a + b + c + d))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
