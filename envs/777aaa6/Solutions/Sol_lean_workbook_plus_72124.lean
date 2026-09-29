-- Prove2me | solution 1 for lean_workbook_plus_72124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:25.159789+00:00
-- url     : https://prove2.me/submissions/aa68539d-d96c-4f5b-bb63-ca3292bce462

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x * (y + z) * (x + y + z) = 1) : (x + y + z) ^ 3 ≥ 4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) ≤ (z) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (z) - (0) := by linarith only [p2m_cond_2]
  have p2m_cond_3 : (x * (y + z) * (x + y + z) : ℝ) = (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (1) - (x * (y + z) * (x + y + z)) = 0 := by linarith only [p2m_cond_3]
  have h_identity : ((x + y + z) ^ 3) - (4) = (1 : ℝ) * ((x) - (0)) * ((x + ((-1) * y) + ((-1) * z)))^2 + (1 : ℝ) * ((y) - (0)) * ((x + ((-1) * y) + ((-1) * z)))^2 + (1 : ℝ) * ((z) - (0)) * ((x + ((-1) * y) + ((-1) * z)))^2 := by
    linear_combination ((-4)) * p2m_cond_3_gap
  have h_nonnegative : (0 : ℝ) ≤ ((x + y + z) ^ 3) - (4) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
