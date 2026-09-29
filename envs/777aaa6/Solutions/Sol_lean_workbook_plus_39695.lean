-- Prove2me | solution 1 for lean_workbook_plus_39695
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:32.34945+00:00
-- url     : https://prove2.me/submissions/b607dcce-f03b-4b5b-b215-2eb44b34b4b6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (p q x y : ℝ) (hp : 0 < p) (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) : (x ^ 2 / p + y ^ 2 / q) ≥ (x + y) ^ 2 / (p + q) := by
  intros
  
  have h_identity : (((p ^ 2) * (y ^ 2)) + ((q ^ 2) * (x ^ 2)) + ((-2) * p * q * x * y)) = (1 : ℝ) * 1 * (((p * y) + ((-1) * q * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((p ^ 2) * (y ^ 2)) + ((q ^ 2) * (x ^ 2)) + ((-2) * p * q * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (p * q * (p + q)) := by positivity
  have h_rational : ((x ^ 2 / p + y ^ 2 / q)) - ((x + y) ^ 2 / (p + q)) = ((((p ^ 2) * (y ^ 2)) + ((q ^ 2) * (x ^ 2)) + ((-2) * p * q * x * y))) / ((p * q * (p + q))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
