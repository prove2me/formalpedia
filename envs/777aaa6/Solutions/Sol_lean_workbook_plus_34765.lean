-- Prove2me | solution 1 for lean_workbook_plus_34765
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:22.603467+00:00
-- url     : https://prove2.me/submissions/5673d6ad-25b0-4541-87fd-321eaa103315

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ∧ a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c) := by
  intro a b c
  intros
  constructor
  · intros
    
    have h_identity : ((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * (a ^ 2) * (b ^ 2)) + ((-1) * (a ^ 2) * (c ^ 2)) + ((-1) * (b ^ 2) * (c ^ 2))) = (1 : ℝ) * 1 * (((a ^ 2) + ((-1 / 2) * (b ^ 2)) + ((-1 / 2) * (c ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * (((b ^ 2) + ((-1) * (c ^ 2))))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ ((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * (a ^ 2) * (b ^ 2)) + ((-1) * (a ^ 2) * (c ^ 2)) + ((-1) * (b ^ 2) * (c ^ 2))) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 1 := by positivity
    have h_rational : (a ^ 4 + b ^ 4 + c ^ 4) - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) = (((a ^ 4) + (b ^ 4) + (c ^ 4) + ((-1) * (a ^ 2) * (b ^ 2)) + ((-1) * (a ^ 2) * (c ^ 2)) + ((-1) * (b ^ 2) * (c ^ 2)))) / (1) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · intros
    
    have h_identity : (((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (c ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-1) * a * b * (c ^ 2)) + ((-1) * a * c * (b ^ 2)) + ((-1) * b * c * (a ^ 2))) = (1 : ℝ) * 1 * (((a * b) + ((-1 / 2) * a * c) + ((-1 / 2) * b * c)))^2 + ((3 / 4) : ℝ) * 1 * (((a * c) + ((-1) * b * c)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (c ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-1) * a * b * (c ^ 2)) + ((-1) * a * c * (b ^ 2)) + ((-1) * b * c * (a ^ 2))) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 1 := by positivity
    have h_rational : (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a * b * c * (a + b + c)) = ((((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (c ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-1) * a * b * (c ^ 2)) + ((-1) * a * c * (b ^ 2)) + ((-1) * b * c * (a ^ 2)))) / (1) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
