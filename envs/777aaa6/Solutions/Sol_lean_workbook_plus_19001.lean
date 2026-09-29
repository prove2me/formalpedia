-- Prove2me | solution 1 for lean_workbook_plus_19001
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:40.203039+00:00
-- url     : https://prove2.me/submissions/4577e413-3c22-4871-b336-c98b213f7af9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x) : ((1 + x^3) * (1 + x)^3) / x^3 ≥ 16 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (1 + (x ^ 6) + ((-14) * (x ^ 3)) + (3 * x) + (3 * (x ^ 2)) + (3 * (x ^ 4)) + (3 * (x ^ 5))) = (1 : ℝ) * 1 * ((1 + ((-1) * (x ^ 3))))^2 + (3 : ℝ) * 1 * ((x + ((-1) * (x ^ 2))))^2 + (3 : ℝ) * ((x) - (0)) * ((1 + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 6) + ((-14) * (x ^ 3)) + (3 * x) + (3 * (x ^ 2)) + (3 * (x ^ 4)) + (3 * (x ^ 5))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x ^ 3) := by positivity
  have h_rational : (((1 + x^3) * (1 + x)^3) / x^3) - (16) = ((1 + (x ^ 6) + ((-14) * (x ^ 3)) + (3 * x) + (3 * (x ^ 2)) + (3 * (x ^ 4)) + (3 * (x ^ 5)))) / ((x ^ 3)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
