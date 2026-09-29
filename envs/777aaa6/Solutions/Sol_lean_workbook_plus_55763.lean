-- Prove2me | solution 1 for lean_workbook_plus_55763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:54.328654+00:00
-- url     : https://prove2.me/submissions/9e4abea5-c993-46fb-8572-db8ad228c4fb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) + (b + a) / (c ^ 2 + b * a) ≤ 1 / a + 1 / b + 1 / c := by
  intros
  
  have h_identity : (((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2))) = (1 : ℝ) * 1 * ((((a ^ 2) * (b ^ 2)) + ((-1 / 2) * (a ^ 2) * (c ^ 2)) + ((-1 / 2) * (b ^ 2) * (c ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * ((((a ^ 2) * (c ^ 2)) + ((-1) * (b ^ 2) * (c ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c * ((a ^ 2) + (b * c)) * ((b ^ 2) + (a * c)) * ((c ^ 2) + (a * b))) := by positivity
  have h_rational : (1 / a + 1 / b + 1 / c) - ((b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) + (b + a) / (c ^ 2 + b * a)) = ((((a ^ 4) * (b ^ 4)) + ((a ^ 4) * (c ^ 4)) + ((b ^ 4) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 2) * (c ^ 4)) + ((-1) * (a ^ 2) * (b ^ 4) * (c ^ 2)) + ((-1) * (a ^ 4) * (b ^ 2) * (c ^ 2)))) / ((a * b * c * ((a ^ 2) + (b * c)) * ((b ^ 2) + (a * c)) * ((c ^ 2) + (a * b)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
