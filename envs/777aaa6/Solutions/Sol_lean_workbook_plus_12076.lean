-- Prove2me | solution 1 for lean_workbook_plus_12076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:23.132805+00:00
-- url     : https://prove2.me/submissions/3b21665f-f8a3-470d-b652-1f6dc41bedfe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a>0 ∧ b>0 ∧ c>0 ∧ a * b * c > 1) :
  a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b + b * c + a * c := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (1 : ℝ) < (a * b * c) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (a * b * c) - (1) := by linarith only [p2m_cond_3]
  have h_identity : (a ^ 3 + b ^ 3 + c ^ 3) - (a * b + b * c + a * c) = ((2 / 3) : ℝ) * 1 * ((1 + ((-1) * b)))^2 + ((1 / 3) : ℝ) * 1 * ((1 + ((-1) * c)))^2 + ((2 / 3) : ℝ) * ((a) - (0)) * ((a + ((-1) * b)))^2 + ((1 / 3) : ℝ) * ((a) - (0)) * ((a + ((-1) * c)))^2 + ((1 / 2) : ℝ) * ((b) - (0)) * ((1 + ((-1) * a)))^2 + ((1 / 3) : ℝ) * ((b) - (0)) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((b) - (0)) * ((1 + ((-1) * c)))^2 + ((1 / 3) : ℝ) * ((b) - (0)) * ((a + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + ((1 / 3) : ℝ) * ((b) - (0)) * ((b + ((-1) * c)))^2 + ((1 / 2) : ℝ) * ((c) - (0)) * ((1 + ((-1) * a)))^2 + ((1 / 6) : ℝ) * ((c) - (0)) * ((1 + ((-1) * c)))^2 + ((1 / 6) : ℝ) * ((c) - (0)) * ((a + ((-1) * c)))^2 + ((2 / 3) : ℝ) * ((c) - (0)) * ((b + ((-1) * c)))^2 + (1 : ℝ) * ((a * b * c) - (1)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a ^ 3 + b ^ 3 + c ^ 3) - (a * b + b * c + a * c) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
