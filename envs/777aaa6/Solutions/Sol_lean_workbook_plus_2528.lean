-- Prove2me | solution 1 for lean_workbook_plus_2528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:48.903479+00:00
-- url     : https://prove2.me/submissions/c9b29478-4142-47ea-b82f-9a3d9c7f1bb6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) : (3 / (1 + x) ≤ 3 - 1 / 2 * x ^ 2) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (2) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (2) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (((-1) * (x ^ 2)) + ((-1) * (x ^ 3)) + (6 * x)) = (6 : ℝ) * ((x) - (0)) * ((1 + ((-1 / 2) * x)))^2 + ((5 / 2) : ℝ) * ((2) - (x)) * (x)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((-1) * (x ^ 2)) + ((-1) * (x ^ 3)) + (6 * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (1 + x)) := by positivity
  have h_rational : (3 - 1 / 2 * x ^ 2) - (3 / (1 + x)) = ((((-1) * (x ^ 2)) + ((-1) * (x ^ 3)) + (6 * x))) / ((2 * (1 + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
