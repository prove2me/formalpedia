-- Prove2me | solution 1 for lean_workbook_plus_21501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:28.184122+00:00
-- url     : https://prove2.me/submissions/3f665650-198d-4d28-821c-b55aa8644aa0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / a + a / (b + c) + c / a) ≥ 2 := by
  intros
  
  have h_identity : ((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * b) + ((-2) * a * c) + (2 * b * c)) = (1 : ℝ) * 1 * ((a + ((-1) * b) + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * b) + ((-2) * a * c) + (2 * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * (b + c)) := by positivity
  have h_rational : ((b / a + a / (b + c) + c / a)) - (2) = (((a ^ 2) + (b ^ 2) + (c ^ 2) + ((-2) * a * b) + ((-2) * a * c) + (2 * b * c))) / ((a * (b + c))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
