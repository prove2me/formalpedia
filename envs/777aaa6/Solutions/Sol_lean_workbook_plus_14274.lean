-- Prove2me | solution 1 for lean_workbook_plus_14274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:11.283387+00:00
-- url     : https://prove2.me/submissions/2ab8abd6-4b5a-429f-a86c-79c082dc296e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 4 * (a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2) ≥ 4 * (a * b + b * c + c * a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (a * b * c : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (a * b * c) = 0 := by linarith only [p2m_cond_3]
  have h_identity : (4 * (a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2)) - (4 * (a * b + b * c + c * a)) = (4 : ℝ) * ((a) - (0)) * (((a * b) + ((-1) * b * c)))^2 + (4 : ℝ) * ((b) - (0)) * (((a * c) + ((-1) * b * c)))^2 + (4 : ℝ) * ((c) - (0)) * (((a * b) + ((-1) * a * c)))^2 := by
    linear_combination ((((-4) * a * b) + ((-4) * a * c) + ((-4) * b * c))) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ (4 * (a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2)) - (4 * (a * b + b * c + c * a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
