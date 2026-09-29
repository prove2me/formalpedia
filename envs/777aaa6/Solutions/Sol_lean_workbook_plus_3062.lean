-- Prove2me | solution 1 for lean_workbook_plus_3062
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:00.007804+00:00
-- url     : https://prove2.me/submissions/57a2297c-0c5f-44d6-86de-4812bd6efcb7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {p : ℝ} (hp : p ≥ 3) : 2 * (4 / 5 - 3 * (p ^ 2 - 6) / (5 * p ^ 2)) ≥ 3 - 3 * p / 5 := by
  intros
  have p2m_cond_0 : (3 : ℝ) ≤ (p) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (p) - (3) := by linarith only [p2m_cond_0]
  have h_identity : (36 + ((-13) * (p ^ 2)) + (3 * (p ^ 3))) = (72 : ℝ) * 1 * ((1 + ((-1 / 3) * p)))^2 + (12 : ℝ) * ((p) - (3)) * ((1 + ((-1 / 2) * p)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (36 + ((-13) * (p ^ 2)) + (3 * (p ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (5 * (p ^ 2)) := by positivity
  have h_rational : (2 * (4 / 5 - 3 * (p ^ 2 - 6) / (5 * p ^ 2))) - (3 - 3 * p / 5) = ((36 + ((-13) * (p ^ 2)) + (3 * (p ^ 3)))) / ((5 * (p ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
