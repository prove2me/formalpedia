-- Prove2me | solution 1 for lean_workbook_plus_34982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:34.460231+00:00
-- url     : https://prove2.me/submissions/65826e2a-0b63-41a1-b763-5b61144a7ab1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx: x ≥ 0 ∧ y ≥ 0 ∧ x + 2*y ≤ 3): x*y^2 ≤ 1 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (x + 2*y : ℝ) ≤ (3) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (3) - (x + 2*y) := by linarith only [p2m_cond_2]
  have h_identity : (1) - (x*y^2) = ((1 / 12) : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + ((2 / 21) : ℝ) * ((y) - (0)) * ((1 + ((-1) * y)))^2 + ((2 / 7) : ℝ) * ((y) - (0)) * ((x + ((-1) * y)))^2 + ((11 / 56) : ℝ) * ((3) - (x + 2*y)) * (1)^2 + ((1 / 24) : ℝ) * ((3) - (x + 2*y)) * ((1 + x))^2 + ((2 / 21) : ℝ) * ((3) - (x + 2*y)) * ((1 + y))^2 + ((1 / 42) : ℝ) * ((3) - (x + 2*y)) * ((x + y))^2 + ((1 / 56) : ℝ) * ((3) - (x + 2*y)) * ((x + (2 * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1) - (x*y^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
