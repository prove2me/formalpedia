-- Prove2me | solution 1 for lean_workbook_plus_42963
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:31.542861+00:00
-- url     : https://prove2.me/submissions/fbd68c8a-9fe3-44a2-a757-4d9b03a7e15b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a / b + b / a + 2) ≥ 4 * (1 + a^2) * (1 + b^2) / (1 + a * b)^2 := by
  intros
  
  have h_identity : ((a ^ 2) + (b ^ 2) + ((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((-2) * a * b) + ((-2) * a * (b ^ 3)) + ((-2) * b * (a ^ 3)) + ((-2) * (a ^ 3) * (b ^ 3)) + (4 * (a ^ 2) * (b ^ 2))) = (1 : ℝ) * 1 * ((a + ((-1) * b) + (a * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 2) + (b ^ 2) + ((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((-2) * a * b) + ((-2) * a * (b ^ 3)) + ((-2) * b * (a ^ 3)) + ((-2) * (a ^ 3) * (b ^ 3)) + (4 * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * ((1 + (a * b)) ^ 2)) := by positivity
  have h_rational : ((a / b + b / a + 2)) - (4 * (1 + a^2) * (1 + b^2) / (1 + a * b)^2) = (((a ^ 2) + (b ^ 2) + ((a ^ 2) * (b ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((-2) * a * b) + ((-2) * a * (b ^ 3)) + ((-2) * b * (a ^ 3)) + ((-2) * (a ^ 3) * (b ^ 3)) + (4 * (a ^ 2) * (b ^ 2)))) / ((a * b * ((1 + (a * b)) ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
