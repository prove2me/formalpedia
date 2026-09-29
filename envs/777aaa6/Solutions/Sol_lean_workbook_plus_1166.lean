-- Prove2me | solution 1 for lean_workbook_plus_1166
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:23.38143+00:00
-- url     : https://prove2.me/submissions/bd6818cd-2eb2-4619-a726-487c081e4381

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a : ℝ) (ha : 0 < a) : (a + 2) ^ 3 / (27 * a) ≥ 1 / 4 + (a + 2) * (2 * a + 1) / (12 * a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (14 + ((-24) * a) + (4 * (a ^ 3)) + (6 * (a ^ 2))) = (14 : ℝ) * 1 * ((1 + ((-1) * a)))^2 + (4 : ℝ) * ((a) - (0)) * ((1 + ((-1) * a)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (14 + ((-24) * a) + (4 * (a ^ 3)) + (6 * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (108 * a) := by positivity
  have h_rational : ((a + 2) ^ 3 / (27 * a)) - (1 / 4 + (a + 2) * (2 * a + 1) / (12 * a)) = ((14 + ((-24) * a) + (4 * (a ^ 3)) + (6 * (a ^ 2)))) / ((108 * a)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
