-- Prove2me | solution 1 for lean_workbook_plus_19328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:59.569752+00:00
-- url     : https://prove2.me/submissions/7dd60cc2-ae7c-417c-8b4f-8a0dadc94d8f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hy : 0 < y) : (a * x / (a + x) + b * y / (b + y)) ≤ (a + b) * (x + y) / (a + b + x + y) := by
  intros
  
  have h_identity : (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) = (1 : ℝ) * 1 * (((a * y) + ((-1) * b * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + x) * (b + y) * (a + b + x + y)) := by positivity
  have h_rational : ((a + b) * (x + y) / (a + b + x + y)) - ((a * x / (a + x) + b * y / (b + y))) = ((((a ^ 2) * (y ^ 2)) + ((b ^ 2) * (x ^ 2)) + ((-2) * a * b * x * y))) / (((a + x) * (b + y) * (a + b + x + y))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
