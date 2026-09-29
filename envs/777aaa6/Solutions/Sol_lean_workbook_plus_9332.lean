-- Prove2me | solution 1 for lean_workbook_plus_9332
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:38.556711+00:00
-- url     : https://prove2.me/submissions/03c00058-9cc7-439a-bdec-ecb1d7ac792d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 8 * (a + b + c) ^ 3 ≥ (7 * a - b) * (7 * b - c) * (7 * c - a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (8 * (a + b + c) ^ 3) - ((7 * a - b) * (7 * b - c) * (7 * c - a)) = (8 : ℝ) * ((a) - (0)) * ((a + ((-5 / 3) * c) + ((2 / 3) * b)))^2 + ((361 / 9) : ℝ) * ((a) - (0)) * ((b + ((-1) * c)))^2 + ((187 / 3) : ℝ) * ((b) - (0)) * ((a + ((-147 / 187) * c) + ((-40 / 187) * b)))^2 + ((2888 / 561) : ℝ) * ((b) - (0)) * ((b + ((-1) * c)))^2 + ((131 / 3) : ℝ) * ((c) - (0)) * ((a + ((-147 / 131) * b) + ((16 / 131) * c)))^2 + ((2888 / 393) : ℝ) * ((c) - (0)) * ((b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (8 * (a + b + c) ^ 3) - ((7 * a - b) * (7 * b - c) * (7 * c - a)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
