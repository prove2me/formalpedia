-- Prove2me | solution 1 for lean_workbook_plus_39869
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:11.672385+00:00
-- url     : https://prove2.me/submissions/f1718027-d581-4230-818c-53fa4921ef1c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  1 / (1 / a + 1 / b) + 1 / (1 / c + 1 / d) ≤ (a + b + c + d) / 4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (0 : ℝ) < (d) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (d) - (0) := by linarith only [p2m_cond_3]
  have h_identity : ((a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (d * (a ^ 2)) + (d * (b ^ 2)) + ((-2) * a * b * c) + ((-2) * a * b * d) + ((-2) * a * c * d) + ((-2) * b * c * d)) = (1 : ℝ) * ((a) - (0)) * ((c + ((-1) * d)))^2 + (1 : ℝ) * ((b) - (0)) * ((c + ((-1) * d)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 + (1 : ℝ) * ((d) - (0)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (d * (a ^ 2)) + (d * (b ^ 2)) + ((-2) * a * b * c) + ((-2) * a * b * d) + ((-2) * a * c * d) + ((-2) * b * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * (a + b) * (c + d)) := by positivity
  have h_rational : ((a + b + c + d) / 4) - (1 / (1 / a + 1 / b) + 1 / (1 / c + 1 / d)) = (((a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + (d * (a ^ 2)) + (d * (b ^ 2)) + ((-2) * a * b * c) + ((-2) * a * b * d) + ((-2) * a * c * d) + ((-2) * b * c * d))) / ((4 * (a + b) * (c + d))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
