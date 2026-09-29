-- Prove2me | solution 1 for lean_workbook_plus_19133
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:08.783768+00:00
-- url     : https://prove2.me/submissions/1e1ad416-93b3-4365-b3f3-703dca969be3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + 2 * y = 2) : (x + 1 / y) * (y + 1 / x) ≥ 9 / 2 := by
  intros
  have p2m_cond_2 : (x + 2 * y : ℝ) = (2) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (2) - (x + 2 * y) = 0 := by linarith only [p2m_cond_2]
  have h_identity : (2 + ((-5) * x * y) + (2 * (x ^ 2) * (y ^ 2))) = ((1 / 2) : ℝ) * 1 * ((1 + ((-2) * x * y)))^2 + ((3 / 8) : ℝ) * 1 * ((x + ((-2) * y)))^2 := by
    linear_combination (((3 / 4) + ((3 / 4) * y) + ((3 / 8) * x))) * p2m_cond_2_gap
  have h_nonnegative : (0 : ℝ) ≤ (2 + ((-5) * x * y) + (2 * (x ^ 2) * (y ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * x * y) := by positivity
  have h_rational : ((x + 1 / y) * (y + 1 / x)) - (9 / 2) = ((2 + ((-5) * x * y) + (2 * (x ^ 2) * (y ^ 2)))) / ((2 * x * y)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
