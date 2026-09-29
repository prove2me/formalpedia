-- Prove2me | solution 1 for lean_workbook_plus_39310
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:57.188384+00:00
-- url     : https://prove2.me/submissions/66441544-b14c-4b43-9229-cab9cab48b80

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (c ^ 2 + a * b) + (b + c) / (a ^ 2 + b * c) + (c + a) / (b ^ 2 + a * c) ≤ 1 / a + 1 / b + 1 / c := by
  intros
  
  have h_identity : (((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2))) = (1 : ℝ) * 1 * ((((a ^ 2) * (b ^ 2)) + ((-1 / 2) * (a ^ 2) * (c ^ 2)) + ((-1 / 2) * (b ^ 2) * (c ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * ((((a ^ 2) * (c ^ 2)) + ((-1) * (b ^ 2) * (c ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c * ((a ^ 2) + (b * c)) * ((b ^ 2) + (a * c)) * ((c ^ 2) + (a * b))) := by positivity
  have h_rational : (1 / a + 1 / b + 1 / c) - ((a + b) / (c ^ 2 + a * b) + (b + c) / (a ^ 2 + b * c) + (c + a) / (b ^ 2 + a * c)) = ((((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2)))) / ((a * b * c * ((a ^ 2) + (b * c)) * ((b ^ 2) + (a * c)) * ((c ^ 2) + (a * b)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
