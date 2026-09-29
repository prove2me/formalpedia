-- Prove2me | solution 1 for lean_workbook_plus_10660
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:32.391427+00:00
-- url     : https://prove2.me/submissions/26c60678-697c-4aff-9946-b620cabc4ede

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y^2 = y^3 + 1) : y + x^2 ≤ x^3 + 1 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (x + y^2 : ℝ) = (y^3 + 1) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (y^3 + 1) - (x + y^2) = 0 := by linarith only [p2m_cond_2]
  have h_identity : (x^3 + 1) - (y + x^2) = (1 : ℝ) * 1 * ((1 + ((-1) * x)))^2 + (1 : ℝ) * 1 * ((1 + ((-1) * y)))^2 + (1 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + (1 : ℝ) * ((y) - (0)) * ((1 + ((-1) * y)))^2 := by
    linear_combination ((-1)) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ (x^3 + 1) - (y + x^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
