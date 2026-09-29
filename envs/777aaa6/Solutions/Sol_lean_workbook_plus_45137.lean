-- Prove2me | solution 1 for lean_workbook_plus_45137
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:59.714097+00:00
-- url     : https://prove2.me/submissions/863454d4-e6cd-468e-88fa-99c46b7472de

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : x^3 ≥ 4 * x - 3 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (x^3) - (4 * x - 3) = (2 : ℝ) * 1 * ((1 + ((-1) * x)))^2 + (1 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + (1 : ℝ) * ((1) - (x)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^3) - (4 * x - 3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
