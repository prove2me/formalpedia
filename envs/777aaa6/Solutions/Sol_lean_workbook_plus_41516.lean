-- Prove2me | solution 1 for lean_workbook_plus_41516
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:25.039915+00:00
-- url     : https://prove2.me/submissions/914079d9-c60f-46dc-b4da-f7532cf1875e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2) ≥ 2 / (x ^ 2 + y ^ 2 + 2) := by
  intros
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (0) := by linarith only [p2m_cond_1]
  have h_identity : (2 + (x ^ 4) + (y ^ 4) + (2 * (x ^ 2)) + (2 * (x ^ 3)) + (2 * (y ^ 2)) + (2 * (y ^ 3)) + ((-8) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2))) = (2 : ℝ) * 1 * ((1 + ((-1) * x * y)))^2 + (2 : ℝ) * 1 * ((x + ((-1) * y)))^2 + (1 : ℝ) * 1 * (((x ^ 2) + ((-1) * (y ^ 2))))^2 + (2 : ℝ) * ((x) - (0)) * ((x + ((-1) * y)))^2 + (2 : ℝ) * ((y) - (0)) * ((x + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 + (x ^ 4) + (y ^ 4) + (2 * (x ^ 2)) + (2 * (x ^ 3)) + (2 * (y ^ 2)) + (2 * (y ^ 3)) + ((-8) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((1 + x) ^ 2) * ((1 + y) ^ 2) * (2 + (x ^ 2) + (y ^ 2))) := by positivity
  have h_rational : ((1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2)) - (2 / (x ^ 2 + y ^ 2 + 2)) = ((2 + (x ^ 4) + (y ^ 4) + (2 * (x ^ 2)) + (2 * (x ^ 3)) + (2 * (y ^ 2)) + (2 * (y ^ 3)) + ((-8) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2)))) / ((((1 + x) ^ 2) * ((1 + y) ^ 2) * (2 + (x ^ 2) + (y ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
