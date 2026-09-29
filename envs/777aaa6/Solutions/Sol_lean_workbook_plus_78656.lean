-- Prove2me | solution 1 for lean_workbook_plus_78656
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:32.14238+00:00
-- url     : https://prove2.me/submissions/7a92bbf4-b479-49fc-9b12-9f265063c019

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (h : x ≥ 1) : x^2 * (x - 1) ≥ x - 1 := by
  intros
  have p2m_cond_0 : (1 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (1) := by linarith only [p2m_cond_0]
  have h_identity : (x^2 * (x - 1)) - (x - 1) = (2 : ℝ) * 1 * ((1 + ((-1) * x)))^2 + (1 : ℝ) * ((x) - (1)) * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x^2 * (x - 1)) - (x - 1) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
