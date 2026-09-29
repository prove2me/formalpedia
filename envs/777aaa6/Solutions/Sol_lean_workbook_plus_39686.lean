-- Prove2me | solution 1 for lean_workbook_plus_39686
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:51.433149+00:00
-- url     : https://prove2.me/submissions/594ffec1-08f9-4afc-a8df-98560a2ac7e2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  (1 - x) / (x ^ 2 + 4 * x + 20) ≤ (1 - x) / 20 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (((-1) * (x ^ 3)) + ((-3) * (x ^ 2)) + (4 * x)) = (4 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 + (5 : ℝ) * ((1) - (x)) * (x)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((-1) * (x ^ 3)) + ((-3) * (x ^ 2)) + (4 * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (20 * (20 + (x ^ 2) + (4 * x))) := by positivity
  have h_rational : ((1 - x) / 20) - ((1 - x) / (x ^ 2 + 4 * x + 20)) = ((((-1) * (x ^ 3)) + ((-3) * (x ^ 2)) + (4 * x))) / ((20 * (20 + (x ^ 2) + (4 * x)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
