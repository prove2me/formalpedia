-- Prove2me | solution 1 for lean_workbook_plus_1662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:20.671765+00:00
-- url     : https://prove2.me/submissions/724ebefa-c6d3-4480-9607-48e39022d200

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution {a b c d : ℝ} : (a + c) * (c + d) * (d + b) * (b + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) ∧ (a + c) * (c + b) * (b + d) * (d + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) := by
  intros
  constructor
  · intros
    
    have h_identity : (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) = (1 : ℝ) * 1 * (((a * d) + ((-1) * b * c)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d)) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 1 := by positivity
    have h_rational : ((a + c) * (c + d) * (d + b) * (b + a)) - ((a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)) = ((((a ^ 2) * (d ^ 2)) + ((b ^ 2) * (c ^ 2)) + ((-2) * a * b * c * d))) / (1) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · intros
    
    have h_identity : (((a ^ 2) * (b ^ 2)) + ((c ^ 2) * (d ^ 2)) + ((-2) * a * b * c * d)) = (1 : ℝ) * 1 * (((a * b) + ((-1) * c * d)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 2)) + ((c ^ 2) * (d ^ 2)) + ((-2) * a * b * c * d)) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 1 := by positivity
    have h_rational : ((a + c) * (c + b) * (b + d) * (d + a)) - ((a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)) = ((((a ^ 2) * (b ^ 2)) + ((c ^ 2) * (d ^ 2)) + ((-2) * a * b * c * d))) / (1) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
