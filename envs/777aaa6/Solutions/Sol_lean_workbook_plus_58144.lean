-- Prove2me | solution 1 for lean_workbook_plus_58144
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:08.345763+00:00
-- url     : https://prove2.me/submissions/bf48aa93-30d0-489a-8d9d-145812086c1c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b x y : ℝ} (hx : x > 0) (hy : y > 0) : (a^2 / x + b^2 / y) ≥ (a + b)^2 / (x + y) := by
  intros
  
  have h_identity : (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) = (1 : ℝ) * 1 * (((a * y) + ((-1) * b * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (x * y * (x + y)) := by positivity
  have h_rational : ((a^2 / x + b^2 / y)) - ((a + b)^2 / (x + y)) = ((((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y))) / ((x * y * (x + y))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
