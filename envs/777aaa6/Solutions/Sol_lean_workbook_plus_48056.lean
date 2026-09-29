-- Prove2me | solution 1 for lean_workbook_plus_48056
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:08.653823+00:00
-- url     : https://prove2.me/submissions/e824888f-5b4a-4ad6-987a-390a4a7550ba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution (a b c : ℝ) : 0 ≤ (1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2)) ∧ (1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2)) ≤ 4 := by
  intros
  constructor
  · intros
    
    have h_identity : (1 + (a ^ 2) + (b ^ 2) + ((-2) * a) + ((-2) * b) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2)) + (4 * a * b)) = (1 : ℝ) * 1 * ((1 + ((-1) * a) + ((-1) * b) + (a * b)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (1 + (a ^ 2) + (b ^ 2) + ((-2) * a) + ((-2) * b) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2)) + (4 * a * b)) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < ((1 + (a ^ 2)) * (1 + (b ^ 2))) := by positivity
    have h_rational : ((1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2))) - (0) = ((1 + (a ^ 2) + (b ^ 2) + ((-2) * a) + ((-2) * b) + ((a ^ 2) * (b ^ 2)) + ((-2) * a * (b ^ 2)) + ((-2) * b * (a ^ 2)) + (4 * a * b))) / (((1 + (a ^ 2)) * (1 + (b ^ 2)))) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · intros
    
    have h_identity : (3 + (2 * a) + (2 * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((-4) * a * b) + (2 * a * (b ^ 2)) + (2 * b * (a ^ 2)) + (3 * (a ^ 2) * (b ^ 2))) = (3 : ℝ) * 1 * ((1 + ((1 / 3) * a) + ((1 / 3) * b) + ((-1 / 3) * a * b)))^2 + ((8 / 3) : ℝ) * 1 * ((a + ((-1 / 2) * b) + ((1 / 2) * a * b)))^2 + (2 : ℝ) * 1 * ((b + (a * b)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (3 + (2 * a) + (2 * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((-4) * a * b) + (2 * a * (b ^ 2)) + (2 * b * (a ^ 2)) + (3 * (a ^ 2) * (b ^ 2))) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < ((1 + (a ^ 2)) * (1 + (b ^ 2))) := by positivity
    have h_rational : (4) - ((1 - a) * (1 - b) * (1 - a - b + a * b) / ((1 + a ^ 2) * (1 + b ^ 2))) = ((3 + (2 * a) + (2 * b) + (3 * (a ^ 2)) + (3 * (b ^ 2)) + ((-4) * a * b) + (2 * a * (b ^ 2)) + (2 * b * (a ^ 2)) + (3 * (a ^ 2) * (b ^ 2)))) / (((1 + (a ^ 2)) * (1 + (b ^ 2)))) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
