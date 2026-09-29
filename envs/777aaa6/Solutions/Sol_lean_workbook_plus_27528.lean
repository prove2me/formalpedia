-- Prove2me | solution 1 for lean_workbook_plus_27528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:53.330136+00:00
-- url     : https://prove2.me/submissions/f38c4474-d016-4f37-81ff-a4eaec070d23

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) : (2 / (3 * x ^ 2) + 3 / (2 * y ^ 2) ≥ 2 / (x * y)) := by
  by_cases hx : x=0
  · subst x
    simpa only [pow_two, zero_mul, mul_zero, div_zero, zero_add] using (div_nonneg (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ 2*y^2))
  by_cases hy : y=0
  · subst y
    simpa only [pow_two, zero_mul, mul_zero, div_zero, add_zero] using (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 3*x^2))
  intros
  
  have h_identity : ((4 * (y ^ 2)) + (9 * (x ^ 2)) + ((-12) * x * y)) = (9 : ℝ) * 1 * ((x + ((-2 / 3) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((4 * (y ^ 2)) + (9 * (x ^ 2)) + ((-12) * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (6 * (x ^ 2) * (y ^ 2)) := by positivity
  have h_rational : (2 / (3 * x ^ 2) + 3 / (2 * y ^ 2)) - (2 / (x * y)) = (((4 * (y ^ 2)) + (9 * (x ^ 2)) + ((-12) * x * y))) / ((6 * (x ^ 2) * (y ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
