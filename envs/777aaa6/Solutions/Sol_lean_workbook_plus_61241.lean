-- Prove2me | solution 1 for lean_workbook_plus_61241
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:31.09146+00:00
-- url     : https://prove2.me/submissions/dcd417b4-9351-4338-a14d-bb19022aa7bd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1): 3 * (a + b + c + d) ≤ 8 + a^3 + b^3 + c^3 + d^3 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_2 : (0 : ℝ) ≤ (b) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_4 : (0 : ℝ) ≤ (c) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_4]
  have p2m_cond_6 : (0 : ℝ) ≤ (d) := by first | assumption | aesop | linarith
  have p2m_cond_6_gap : (0 : ℝ) ≤ (d) - (0) := by linarith only [p2m_cond_6]
  have h_identity : (8 + a^3 + b^3 + c^3 + d^3) - (3 * (a + b + c + d)) = (2 : ℝ) * 1 * ((1 + ((-1) * a)))^2 + (2 : ℝ) * 1 * ((1 + ((-1) * b)))^2 + (2 : ℝ) * 1 * ((1 + ((-1) * c)))^2 + (2 : ℝ) * 1 * ((1 + ((-1) * d)))^2 + (1 : ℝ) * ((a) - (0)) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((b) - (0)) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * ((c) - (0)) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((d) - (0)) * ((1 + ((-1) * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (8 + a^3 + b^3 + c^3 + d^3) - (3 * (a + b + c + d)) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
