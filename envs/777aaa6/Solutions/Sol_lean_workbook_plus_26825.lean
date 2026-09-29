-- Prove2me | solution 1 for lean_workbook_plus_26825
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:47.844967+00:00
-- url     : https://prove2.me/submissions/5f00c60b-a763-4a52-8bd7-05d69ebc83f4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (t : ℝ) (ht : 0 < t) : (t + 2) / (t * (t + 4)) ≥ (22 - 5 * t) / 36 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (t) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (t) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (72 + ((-52) * t) + ((-2) * (t ^ 2)) + (5 * (t ^ 3))) = (72 : ℝ) * 1 * ((1 + ((-1 / 2) * t)))^2 + (20 : ℝ) * ((t) - (0)) * ((1 + ((-1 / 2) * t)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (72 + ((-52) * t) + ((-2) * (t ^ 2)) + (5 * (t ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (36 * t * (4 + t)) := by positivity
  have h_rational : ((t + 2) / (t * (t + 4))) - ((22 - 5 * t) / 36) = ((72 + ((-52) * t) + ((-2) * (t ^ 2)) + (5 * (t ^ 3)))) / ((36 * t * (4 + t))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
