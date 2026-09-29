-- Prove2me | solution 1 for lean_workbook_plus_279
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:32.223702+00:00
-- url     : https://prove2.me/submissions/723bad4f-1422-43a6-a52f-123f7ad5c454

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + b + c + d) ^ 3 ≥ 4 * (a * (c + d) ^ 2 + b * (d + a) ^ 2 + c * (a + b) ^ 2 + d * (b + c) ^ 2) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (0 : ℝ) ≤ (d) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (d) - (0) := by linarith only [p2m_cond_3]
  have h_identity : ((a + b + c + d) ^ 3) - (4 * (a * (c + d) ^ 2 + b * (d + a) ^ 2 + c * (a + b) ^ 2 + d * (b + c) ^ 2)) = (1 : ℝ) * ((a) - (0)) * ((a + d + ((-1) * b) + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + b + ((-1) * c) + ((-1) * d)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + d + ((-1) * b) + ((-1) * c)))^2 + (1 : ℝ) * ((d) - (0)) * ((a + b + ((-1) * c) + ((-1) * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a + b + c + d) ^ 3) - (4 * (a * (c + d) ^ 2 + b * (d + a) ^ 2 + c * (a + b) ^ 2 + d * (b + c) ^ 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
