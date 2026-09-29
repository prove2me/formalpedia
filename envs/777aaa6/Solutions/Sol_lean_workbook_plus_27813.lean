-- Prove2me | solution 1 for lean_workbook_plus_27813
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:51.380609+00:00
-- url     : https://prove2.me/submissions/1e323a3b-7869-4b1b-8aeb-ee30ab765c1a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution (a b c: ℝ) (h : a * b + b * c + c * a = 1) :
  a * a + b * b ≥ 1 - c * c ∧ b * b + c * c ≥ 1 - a * a ∧ c * c + a * a ≥ 1 - b * b := by
  intros
  constructor
  · intros
    have p2m_cond_0 : (a * b + b * c + c * a : ℝ) = (1) := by first | assumption | aesop | linarith
    have p2m_cond_0_gap : (1) - (a * b + b * c + c * a) = 0 := by linarith only [p2m_cond_0]
    have h_identity : ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) = (1 : ℝ) * 1 * ((a + ((-1 / 2) * b) + ((-1 / 2) * c)))^2 + ((3 / 4) : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
      linear_combination ((-1)) * p2m_cond_0_gap
    have h_nonnegative : (0 : ℝ) ≤ ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < 1 := by positivity
    have h_rational : (a * a + b * b) - (1 - c * c) = (((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2))) / (1) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · constructor
    · intros
      have p2m_cond_0 : (a * b + b * c + c * a : ℝ) = (1) := by first | assumption | aesop | linarith
      have p2m_cond_0_gap : (1) - (a * b + b * c + c * a) = 0 := by linarith only [p2m_cond_0]
      have h_identity : ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) = (1 : ℝ) * 1 * ((a + ((-1 / 2) * b) + ((-1 / 2) * c)))^2 + ((3 / 4) : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
        linear_combination ((-1)) * p2m_cond_0_gap
      have h_nonnegative : (0 : ℝ) ≤ ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) := by
        rw [h_identity]
        positivity
      have h_denominator : (0 : ℝ) < 1 := by positivity
      have h_rational : (b * b + c * c) - (1 - a * a) = (((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2))) / (1) := by
        field_simp (disch := first | positivity | linarith | aesop)
        <;> ring
      apply sub_nonneg.mp
      rw [h_rational]
      exact div_nonneg h_nonnegative (le_of_lt h_denominator)
    · intros
      have p2m_cond_0 : (a * b + b * c + c * a : ℝ) = (1) := by first | assumption | aesop | linarith
      have p2m_cond_0_gap : (1) - (a * b + b * c + c * a) = 0 := by linarith only [p2m_cond_0]
      have h_identity : ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) = (1 : ℝ) * 1 * ((a + ((-1 / 2) * b) + ((-1 / 2) * c)))^2 + ((3 / 4) : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
        linear_combination ((-1)) * p2m_cond_0_gap
      have h_nonnegative : (0 : ℝ) ≤ ((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2)) := by
        rw [h_identity]
        positivity
      have h_denominator : (0 : ℝ) < 1 := by positivity
      have h_rational : (c * c + a * a) - (1 - b * b) = (((-1) + (a ^ 2) + (b ^ 2) + (c ^ 2))) / (1) := by
        field_simp (disch := first | positivity | linarith | aesop)
        <;> ring
      apply sub_nonneg.mp
      rw [h_rational]
      exact div_nonneg h_nonnegative (le_of_lt h_denominator)
