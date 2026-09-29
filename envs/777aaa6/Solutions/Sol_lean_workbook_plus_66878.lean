-- Prove2me | solution 1 for lean_workbook_plus_66878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:41.97171+00:00
-- url     : https://prove2.me/submissions/375b3557-92a1-4b63-ab17-75c9ca1f78d0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : x > 0) : x^2 + 1 / (4 * x) ≥ 3 / 4 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (1 + ((-3) * x) + (4 * (x ^ 3))) = (1 : ℝ) * 1 * ((1 + ((-2) * x)))^2 + (1 : ℝ) * ((x) - (0)) * ((1 + ((-2) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((-3) * x) + (4 * (x ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * x) := by positivity
  have h_rational : (x^2 + 1 / (4 * x)) - (3 / 4) = ((1 + ((-3) * x) + (4 * (x ^ 3)))) / ((4 * x)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
