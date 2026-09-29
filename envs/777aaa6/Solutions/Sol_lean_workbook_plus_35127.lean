-- Prove2me | solution 1 for lean_workbook_plus_35127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:54.852974+00:00
-- url     : https://prove2.me/submissions/c3f7e2e9-b70f-4a15-9d5b-b98047b528fe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 ≤ x) : 1 / (1 + x ^ 2) ≥ (2 - x) / 2 := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (x + (x ^ 3) + ((-2) * (x ^ 2))) = (1 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x + (x ^ 3) + ((-2) * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (1 + (x ^ 2))) := by positivity
  have h_rational : (1 / (1 + x ^ 2)) - ((2 - x) / 2) = ((x + (x ^ 3) + ((-2) * (x ^ 2)))) / ((2 * (1 + (x ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
