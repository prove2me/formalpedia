-- Prove2me | solution 1 for lean_workbook_plus_38134
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:54.762925+00:00
-- url     : https://prove2.me/submissions/68851d0f-1eab-40cc-885d-ac347b2a59eb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (1 + a + a * b) + b / (1 + b + b * c) + c / (1 + c + c * a) ≤ 1 := by
  intros
  
  have h_identity : (1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c)) = (1 : ℝ) * 1 * ((1 + ((-1) * a * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + a + (a * b)) * (1 + b + (b * c)) * (1 + c + (a * c))) := by positivity
  have h_rational : (1) - (a / (1 + a + a * b) + b / (1 + b + b * c) + c / (1 + c + c * a)) = ((1 + ((a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * c))) / (((1 + a + (a * b)) * (1 + b + (b * c)) * (1 + c + (a * c)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
