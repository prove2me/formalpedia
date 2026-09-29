-- Prove2me | solution 1 for lean_workbook_plus_12925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:33.375676+00:00
-- url     : https://prove2.me/submissions/4c6fcc20-25a0-4c28-bdeb-1c7d4841d57d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 6 * t ^ 5 - 15 * t ^ 4 + 6 * t ^ 3 + 6 * t ^ 2 - 4 * t + 1 ≥ 0 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (t) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (t) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (t : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (t) := by linarith only [p2m_cond_1]
  have h_identity : (6 * t ^ 5 - 15 * t ^ 4 + 6 * t ^ 3 + 6 * t ^ 2 - 4 * t + 1) - (0) = ((1 / 4) : ℝ) * 1 * ((1 + ((-1) * t)))^2 + ((15 / 2) : ℝ) * ((t) - (0)) * ((t + ((-1) * (t ^ 2))))^2 + ((1 / 8) : ℝ) * ((1) - (t)) * ((1 + ((-1) * t)))^2 + ((5 / 8) : ℝ) * ((1) - (t)) * ((1 + ((-2) * t)))^2 + ((3 / 8) : ℝ) * ((1) - (t)) * ((t + (2 * (t ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (6 * t ^ 5 - 15 * t ^ 4 + 6 * t ^ 3 + 6 * t ^ 2 - 4 * t + 1) - (0) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
