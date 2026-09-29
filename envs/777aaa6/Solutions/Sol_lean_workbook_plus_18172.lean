-- Prove2me | solution 1 for lean_workbook_plus_18172
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:02.877745+00:00
-- url     : https://prove2.me/submissions/362c1145-b7cc-40b6-a749-b9a391bf1a04

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 15 * (a ^ 3 + b ^ 3 + c ^ 3 + (a * b + b * c + c * a) * (a + b + c)) + 9 * a * b * c - 7 * (a + b + c) ^ 3 ≥ 0 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (15 * (a ^ 3 + b ^ 3 + c ^ 3 + (a * b + b * c + c * a) * (a + b + c)) + 9 * a * b * c - 7 * (a + b + c) ^ 3) - (0) = (8 : ℝ) * ((a) - (0)) * ((a + ((-1 / 2) * b) + ((-1 / 2) * c)))^2 + (2 : ℝ) * ((b) - (0)) * ((a + c + ((-2) * b)))^2 + (2 : ℝ) * ((c) - (0)) * ((a + b + ((-2) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (15 * (a ^ 3 + b ^ 3 + c ^ 3 + (a * b + b * c + c * a) * (a + b + c)) + 9 * a * b * c - 7 * (a + b + c) ^ 3) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
