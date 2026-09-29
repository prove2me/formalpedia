-- Prove2me | solution 1 for lean_workbook_plus_26915
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:34.286927+00:00
-- url     : https://prove2.me/submissions/f3e15f27-e236-4299-8470-20390712a5c1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution (b c : ℝ) : (8 / 9 * b ^ 2 + 9 / 2) ≥ 4 * b ∧ (8 / 9 * c ^ 2 + 9 / 2) ≥ 4 * c := by
  intros
  constructor
  · intros
    
    have h_identity : (81 + ((-72) * b) + (16 * (b ^ 2))) = (81 : ℝ) * 1 * ((1 + ((-4 / 9) * b)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (81 + ((-72) * b) + (16 * (b ^ 2))) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 18 := by positivity
    have h_rational : ((8 / 9 * b ^ 2 + 9 / 2)) - (4 * b) = ((81 + ((-72) * b) + (16 * (b ^ 2)))) / (18) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · intros
    
    have h_identity : (81 + ((-72) * c) + (16 * (c ^ 2))) = (81 : ℝ) * 1 * ((1 + ((-4 / 9) * c)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (81 + ((-72) * c) + (16 * (c ^ 2))) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 18 := by positivity
    have h_rational : ((8 / 9 * c ^ 2 + 9 / 2)) - (4 * c) = ((81 + ((-72) * c) + (16 * (c ^ 2)))) / (18) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
