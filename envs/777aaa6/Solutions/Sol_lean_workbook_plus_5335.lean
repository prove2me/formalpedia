-- Prove2me | solution 1 for lean_workbook_plus_5335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:59.414531+00:00
-- url     : https://prove2.me/submissions/fe56a717-7d49-4226-b9f0-93a8268a821d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) : (x + 1) * (y + 1) * (x * y + 1) / (x ^ 2 + 1) / (y ^ 2 + 1) ≤ 2 := by
  intros
  
  have h_identity : (1 + ((-1) * x) + ((-1) * y) + (2 * (x ^ 2)) + (2 * (y ^ 2)) + ((x ^ 2) * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (x ^ 2)) + ((-2) * x * y)) = (1 : ℝ) * 1 * ((1 + ((-1 / 2) * x) + ((-1 / 2) * y)))^2 + ((7 / 4) : ℝ) * 1 * ((x + ((-5 / 7) * y) + ((-2 / 7) * x * y)))^2 + ((6 / 7) : ℝ) * 1 * ((((-1) * y) + (x * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + ((-1) * x) + ((-1) * y) + (2 * (x ^ 2)) + (2 * (y ^ 2)) + ((x ^ 2) * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (x ^ 2)) + ((-2) * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + (x ^ 2)) * (1 + (y ^ 2))) := by positivity
  have h_rational : (2) - ((x + 1) * (y + 1) * (x * y + 1) / (x ^ 2 + 1) / (y ^ 2 + 1)) = ((1 + ((-1) * x) + ((-1) * y) + (2 * (x ^ 2)) + (2 * (y ^ 2)) + ((x ^ 2) * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (x ^ 2)) + ((-2) * x * y))) / (((1 + (x ^ 2)) * (1 + (y ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
