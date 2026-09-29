-- Prove2me | solution 1 for lean_workbook_plus_52997
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:03.407716+00:00
-- url     : https://prove2.me/submissions/2bf97f19-a6a5-4437-beb3-ed7e09c14b02

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (h : x + y > 1) :
  (x * y * (2 + x + y)) / ((1 + x) * (1 + y)) ≤ (1 + x + y) / 3 := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_y : (0 : ℝ) < y := by grind
  
  have p2m_cond_1 : (x : ℝ) < (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have p2m_cond_3 : (y : ℝ) < (1) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (1) - (y) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (1 : ℝ) < (x + y) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (x + y) - (1) := by linarith only [p2m_cond_4]
  have h_identity : (1 + (x ^ 2) + (y ^ 2) + (2 * x) + (2 * y) + ((-3) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2))) = ((1 / 17) : ℝ) * ((1) - (x)) * ((1 + x))^2 + ((7 / 68) : ℝ) * ((1) - (x)) * ((1 + (2 * x)))^2 + ((29 / 68) : ℝ) * ((1) - (x)) * ((1 + (2 * y)))^2 + ((29 / 68) : ℝ) * ((1) - (y)) * ((1 + (2 * x)))^2 + ((1 / 17) : ℝ) * ((1) - (y)) * ((1 + y))^2 + ((7 / 68) : ℝ) * ((1) - (y)) * ((1 + (2 * y)))^2 + ((3 / 34) : ℝ) * ((x + y) - (1)) * ((1 + ((-1) * x)))^2 + ((3 / 34) : ℝ) * ((x + y) - (1)) * ((1 + ((-1) * y)))^2 + ((13 / 34) : ℝ) * ((x + y) - (1)) * ((x + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 2) + (y ^ 2) + (2 * x) + (2 * y) + ((-3) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (3 * (1 + x) * (1 + y)) := by positivity
  have h_rational : ((1 + x + y) / 3) - ((x * y * (2 + x + y)) / ((1 + x) * (1 + y))) = ((1 + (x ^ 2) + (y ^ 2) + (2 * x) + (2 * y) + ((-3) * x * y) + ((-2) * x * (y ^ 2)) + ((-2) * y * (x ^ 2)))) / ((3 * (1 + x) * (1 + y))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
