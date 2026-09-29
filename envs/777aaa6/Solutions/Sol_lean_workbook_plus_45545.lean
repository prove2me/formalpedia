-- Prove2me | solution 1 for lean_workbook_plus_45545
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:16.626588+00:00
-- url     : https://prove2.me/submissions/5210702f-f32b-4fd0-a12d-2e0522434cf6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (1 / a + 1 / b) + 1 / (1 / c + 1 / d)) ≤ 1 / (1 / (a + c) + 1 / (b + d)) := by
  intros
  
  have h_identity : (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) = (1 : ℝ) * 1 * (((a * d) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + b) * (c + d) * (a + b + c + d)) := by positivity
  have h_rational : (1 / (1 / (a + c) + 1 / (b + d))) - ((1 / (1 / a + 1 / b) + 1 / (1 / c + 1 / d))) = ((((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d))) / (((a + b) * (c + d) * (a + b + c + d))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
