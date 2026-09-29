-- Prove2me | solution 1 for lean_workbook_plus_40593
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:21.853737+00:00
-- url     : https://prove2.me/submissions/6bb1a0ce-7989-4024-9834-d61f7791cac7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y a b : ℝ) (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b) : (x ^ 2 / a + y ^ 2 / b) ≥ (x + y) ^ 2 / (a + b) := by
  intros
  
  have h_identity : (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) = (1 : ℝ) * 1 * (((a * y) + ((-1) * b * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * (a + b)) := by positivity
  have h_rational : ((x ^ 2 / a + y ^ 2 / b)) - ((x + y) ^ 2 / (a + b)) = ((((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y))) / ((a * b * (a + b))) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
