-- Prove2me | solution 1 for lean_workbook_plus_15245
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:27.969597+00:00
-- url     : https://prove2.me/submissions/b6253af0-34f1-427c-b07e-697dd11680f7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 6) :
  x * (x - 6) ^ 2 ≤ 36 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (6) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (6) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (36) - (x * (x - 6) ^ 2) = ((1 / 7) : ℝ) * 1 * (x)^2 + ((1 / 7) : ℝ) * ((x) - (0)) * (x)^2 + (6 : ℝ) * ((6) - (x)) * ((1 + ((-5 / 12) * x)))^2 + ((17 / 168) : ℝ) * ((6) - (x)) * (x)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (36) - (x * (x - 6) ^ 2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
