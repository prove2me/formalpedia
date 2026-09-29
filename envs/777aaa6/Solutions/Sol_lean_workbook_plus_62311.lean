-- Prove2me | solution 1 for lean_workbook_plus_62311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:53.78479+00:00
-- url     : https://prove2.me/submissions/e40f9bb4-c854-4190-90a3-ff9bd043a361

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∧ z > 0) : (x / (x + y) + y / (y + z) + z / (z + x)) ≥ 3 / 2 := by
  intros
  have p2m_pos_x : (0 : ℝ) < x := by grind
  have p2m_pos_y : (0 : ℝ) < y := by grind
  have p2m_pos_z : (0 : ℝ) < z := by grind
  
  have p2m_cond_0 : (y : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (y) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (z : ℝ) ≤ (y) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (y) - (z) := by linarith only [p2m_cond_1]
  have h_identity : ((x * (z ^ 2)) + (y * (x ^ 2)) + (z * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2))) = (1 : ℝ) * ((x) - (y)) * ((y + ((-1) * z)))^2 + (1 : ℝ) * ((y) - (z)) * ((x + ((-1) * y)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((x * (z ^ 2)) + (y * (x ^ 2)) + (z * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (x + y) * (x + z) * (y + z)) := by positivity
  have h_rational : ((x / (x + y) + y / (y + z) + z / (z + x))) - (3 / 2) = (((x * (z ^ 2)) + (y * (x ^ 2)) + (z * (y ^ 2)) + ((-1) * x * (y ^ 2)) + ((-1) * y * (z ^ 2)) + ((-1) * z * (x ^ 2)))) / ((2 * (x + y) * (x + z) * (y + z))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
