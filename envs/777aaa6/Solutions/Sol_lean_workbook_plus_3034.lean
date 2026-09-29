-- Prove2me | solution 1 for lean_workbook_plus_3034
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:52.575123+00:00
-- url     : https://prove2.me/submissions/d9ce0ac6-192e-4335-8d3a-4650215155c5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) : (2 * (1 - x)) / (x * (2 - x)) ≥ (1 / 25) * (138 - 234 * x) := by
  have hx0 : 0 < x := hx.1
  have hx2 : 0 < 2-x := by linarith [hx.2]
  intros
  have p2m_cond_1 : (x : ℝ) < (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (50 + ((-326) * x) + ((-234) * (x ^ 3)) + (606 * (x ^ 2))) = (24 : ℝ) * 1 * ((1 + ((-3) * x)))^2 + (26 : ℝ) * ((1) - (x)) * ((1 + ((-3) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (50 + ((-326) * x) + ((-234) * (x ^ 3)) + (606 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((-25) * x * ((-2) + x)) := by
    have hh : 0 < 25*x*(2-x) := by positivity
    nlinarith only [hh]
  have h_rational : ((2 * (1 - x)) / (x * (2 - x))) - ((1 / 25) * (138 - 234 * x)) = ((50 + ((-326) * x) + ((-234) * (x ^ 3)) + (606 * (x ^ 2)))) / (((-25) * x * ((-2) + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
