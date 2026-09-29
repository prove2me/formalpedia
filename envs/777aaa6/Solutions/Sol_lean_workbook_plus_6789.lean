-- Prove2me | solution 1 for lean_workbook_plus_6789
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:59.503885+00:00
-- url     : https://prove2.me/submissions/ea2f3c69-5d5f-4306-a747-49fb4d4a440e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 + b ^ 2 + c ^ 2 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (a ^ 3 + b ^ 3 + c ^ 3) - (a ^ 2 + b ^ 2 + c ^ 2) = ((1 / 3) : ℝ) * 1 * ((1 + ((-1) * a)))^2 + ((1 / 3) : ℝ) * 1 * ((1 + ((-1) * b)))^2 + ((1 / 3) : ℝ) * 1 * ((1 + ((-1) * c)))^2 + ((2 / 3) : ℝ) * ((a) - (0)) * ((1 + ((-1) * a)))^2 + ((1 / 3) : ℝ) * ((a) - (0)) * ((a + ((-1) * b)))^2 + ((2 / 3) : ℝ) * ((b) - (0)) * ((1 + ((-1) * b)))^2 + ((1 / 6) : ℝ) * ((b) - (0)) * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + ((1 / 6) : ℝ) * ((b) - (0)) * ((b + ((-1) * c)))^2 + ((2 / 3) : ℝ) * ((c) - (0)) * ((1 + ((-1) * c)))^2 + ((1 / 3) : ℝ) * ((c) - (0)) * ((b + ((-1) * c)))^2 := by
    linear_combination ((-1)) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (a ^ 3 + b ^ 3 + c ^ 3) - (a ^ 2 + b ^ 2 + c ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
