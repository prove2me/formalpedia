-- Prove2me | solution 2 for lean_workbook_plus_29447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:57.550313+00:00
-- url     : https://prove2.me/submissions/f0e4c342-c3b3-4c50-b15b-b73e1fbacb27

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
  x + (1 / x ^ 2) ≥ 2 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (1 + (x ^ 3) + ((-2) * (x ^ 2))) = (1 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + (1 : ℝ) * ((1) - (x)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 3) + ((-2) * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x ^ 2) := by positivity
  have h_rational : (x + (1 / x ^ 2)) - (2) = ((1 + (x ^ 3) + ((-2) * (x ^ 2)))) / ((x ^ 2)) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
