-- Prove2me | solution 1 for lean_workbook_plus_46804
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:49.967464+00:00
-- url     : https://prove2.me/submissions/c28dfcd8-39b0-4c11-9f76-e70200b6549c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2 ≥ 4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2) - (4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2)) = (8 : ℝ) * ((a) - (0)) * ((a + ((-1 / 2) * b) + ((-1 / 2) * c)))^2 + (4 : ℝ) * ((b) - (0)) * ((a + ((-3 / 4) * b) + ((-1 / 4) * c)))^2 + ((3 / 4) : ℝ) * ((b) - (0)) * ((b + ((-1) * c)))^2 + (4 : ℝ) * ((c) - (0)) * ((a + ((-3 / 4) * c) + ((-1 / 4) * b)))^2 + ((3 / 4) : ℝ) * ((c) - (0)) * ((b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2) - (4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
