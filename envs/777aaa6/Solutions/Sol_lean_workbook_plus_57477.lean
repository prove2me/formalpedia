-- Prove2me | solution 1 for lean_workbook_plus_57477
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:41.052991+00:00
-- url     : https://prove2.me/submissions/2cda2b91-e4aa-49c2-a8a1-8f521135b98b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
  6303 * t ^ 5 + 3320 * t ^ 4 + 1776 ≥ 5656 * t ^ 3 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (t) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (t) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (t : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (t) := by linarith only [p2m_cond_1]
  have h_identity : (6303 * t ^ 5 + 3320 * t ^ 4 + 1776) - (5656 * t ^ 3) = ((6431 / 176) : ℝ) * 1 * ((1 + (t ^ 2)))^2 + ((224033 / 176) : ℝ) * 1 * ((1 + ((-1) * (t ^ 2))))^2 + ((47217 / 44) : ℝ) * ((t) - (0)) * ((1 + ((-2) * (t ^ 2))))^2 + ((5529 / 11) : ℝ) * ((t) - (0)) * ((t + (2 * (t ^ 2))))^2 + ((55423 / 352) : ℝ) * ((1) - (t)) * ((1 + (2 * t)))^2 + ((9891 / 32) : ℝ) * ((1) - (t)) * ((1 + ((-2) * t)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (6303 * t ^ 5 + 3320 * t ^ 4 + 1776) - (5656 * t ^ 3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
