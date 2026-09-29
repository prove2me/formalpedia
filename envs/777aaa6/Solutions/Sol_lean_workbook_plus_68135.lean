-- Prove2me | solution 1 for lean_workbook_plus_68135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:56.033723+00:00
-- url     : https://prove2.me/submissions/364cd79b-74b9-4be5-b577-46b178ab3b5e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 600000



theorem solution (x y z : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) : (x / y + x / z) ≥ 4 * x / (y + z) ∧ (y / z + y / x) ≥ 4 * y / (z + x) ∧ (z / x + z / y) ≥ 4 * z / (x + y) := by
  intros
  constructor
  · intros
    have p2m_cond_0 : (1 : ℝ) < (x) := by first | assumption | aesop | linarith
    have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (1) := by linarith only [p2m_cond_0]
    have h_identity : ((x * (y ^ 2)) + (x * (z ^ 2)) + ((-2) * x * y * z)) = (1 : ℝ) * 1 * ((y + ((-1) * z)))^2 + (1 : ℝ) * ((x) - (1)) * ((y + ((-1) * z)))^2 := by
      ring
    have h_nonnegative : (0 : ℝ) ≤ ((x * (y ^ 2)) + (x * (z ^ 2)) + ((-2) * x * y * z)) := by
      rw [h_identity]
      positivity
    have h_denominator : (0 : ℝ) < (y * z * (y + z)) := by positivity
    have h_rational : ((x / y + x / z)) - (4 * x / (y + z)) = (((x * (y ^ 2)) + (x * (z ^ 2)) + ((-2) * x * y * z))) / ((y * z * (y + z))) := by
      field_simp (disch := first | positivity | linarith | aesop)
      <;> ring
    apply sub_nonneg.mp
    rw [h_rational]
    exact div_nonneg h_nonnegative (le_of_lt h_denominator)
  · constructor
    · intros
      have p2m_cond_1 : (1 : ℝ) < (y) := by first | assumption | aesop | linarith
      have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (1) := by linarith only [p2m_cond_1]
      have h_identity : ((y * (x ^ 2)) + (y * (z ^ 2)) + ((-2) * x * y * z)) = (1 : ℝ) * 1 * ((x + ((-1) * z)))^2 + (1 : ℝ) * ((y) - (1)) * ((x + ((-1) * z)))^2 := by
        ring
      have h_nonnegative : (0 : ℝ) ≤ ((y * (x ^ 2)) + (y * (z ^ 2)) + ((-2) * x * y * z)) := by
        rw [h_identity]
        positivity
      have h_denominator : (0 : ℝ) < (x * z * (x + z)) := by positivity
      have h_rational : ((y / z + y / x)) - (4 * y / (z + x)) = (((y * (x ^ 2)) + (y * (z ^ 2)) + ((-2) * x * y * z))) / ((x * z * (x + z))) := by
        field_simp (disch := first | positivity | linarith | aesop)
        <;> ring
      apply sub_nonneg.mp
      rw [h_rational]
      exact div_nonneg h_nonnegative (le_of_lt h_denominator)
    · intros
      have p2m_cond_2 : (1 : ℝ) < (z) := by first | assumption | aesop | linarith
      have p2m_cond_2_gap : (0 : ℝ) ≤ (z) - (1) := by linarith only [p2m_cond_2]
      have h_identity : ((z * (x ^ 2)) + (z * (y ^ 2)) + ((-2) * x * y * z)) = (1 : ℝ) * 1 * ((x + ((-1) * y)))^2 + (1 : ℝ) * ((z) - (1)) * ((x + ((-1) * y)))^2 := by
        ring
      have h_nonnegative : (0 : ℝ) ≤ ((z * (x ^ 2)) + (z * (y ^ 2)) + ((-2) * x * y * z)) := by
        rw [h_identity]
        positivity
      have h_denominator : (0 : ℝ) < (x * y * (x + y)) := by positivity
      have h_rational : ((z / x + z / y)) - (4 * z / (x + y)) = (((z * (x ^ 2)) + (z * (y ^ 2)) + ((-2) * x * y * z))) / ((x * y * (x + y))) := by
        field_simp (disch := first | positivity | linarith | aesop)
        <;> ring
      apply sub_nonneg.mp
      rw [h_rational]
      exact div_nonneg h_nonnegative (le_of_lt h_denominator)
