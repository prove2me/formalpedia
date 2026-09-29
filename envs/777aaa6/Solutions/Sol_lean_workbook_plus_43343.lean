-- Prove2me | solution 1 for lean_workbook_plus_43343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:05.152044+00:00
-- url     : https://prove2.me/submissions/eba34e84-16a1-45cf-8fca-6c2a66861903

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (1 + a * (1 + b)) + b / (1 + b * (1 + c)) + c / (1 + c * (1 + a)) ≤ 1 := by
  intros
  
  have h_identity : (1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c)) = (1 : ℝ) * 1 * ((1 + ((-1) * a * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + a + (a * b)) * (1 + b + (b * c)) * (1 + c + (a * c))) := by positivity
  have h_rational : (1) - (a / (1 + a * (1 + b)) + b / (1 + b * (1 + c)) + c / (1 + c * (1 + a))) = ((1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c))) / (((1 + a + (a * b)) * (1 + b + (b * c)) * (1 + c + (a * c)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
