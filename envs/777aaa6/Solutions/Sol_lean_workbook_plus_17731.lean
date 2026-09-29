-- Prove2me | solution 1 for lean_workbook_plus_17731
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:58.929311+00:00
-- url     : https://prove2.me/submissions/9c4caa42-e340-45b8-a65c-e68883959ef6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 3) :
  ((3 - x) ^ 5 + 32) / (x ^ 3 + 1) - 120 + 88 * x ≥ 0 := by
  intros
  have p2m_pos_x : (0 : ℝ) ≤ x := by grind
  have p2m_pos_factor_0 : (0 : ℝ) < 1+x^2-x := by nlinarith [sq_nonneg (2*x-1)]
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (x : ℝ) ≤ (3) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (3) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (155 + ((-1) * (x ^ 5)) + ((-317) * x) + ((-210) * (x ^ 3)) + (103 * (x ^ 4)) + (270 * (x ^ 2))) = ((127 / 6) : ℝ) * ((x) - (0)) * ((1 + ((-1) * (x ^ 2))))^2 + ((191 / 4) : ℝ) * ((3) - (x)) * ((1 + ((-1) * x)))^2 + ((47 / 12) : ℝ) * ((3) - (x)) * ((1 + ((-1) * (x ^ 2))))^2 + ((73 / 4) : ℝ) * ((3) - (x)) * ((x + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (155 + ((-1) * (x ^ 5)) + ((-317) * x) + ((-210) * (x ^ 3)) + (103 * (x ^ 4)) + (270 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((1 + x) * (1 + (x ^ 2) + ((-1) * x))) := by
    convert mul_pos (show (0 : ℝ) < 1+x by positivity) p2m_pos_factor_0 using 1 <;> ring
  have h_rational : (((3 - x) ^ 5 + 32) / (x ^ 3 + 1) - 120 + 88 * x) - (0) = ((155 + ((-1) * (x ^ 5)) + ((-317) * x) + ((-210) * (x ^ 3)) + (103 * (x ^ 4)) + (270 * (x ^ 2)))) / (((1 + x) * (1 + (x ^ 2) + ((-1) * x)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
