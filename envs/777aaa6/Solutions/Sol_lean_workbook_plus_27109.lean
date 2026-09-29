-- Prove2me | solution 1 for lean_workbook_plus_27109
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:07:44.420197+00:00
-- url     : https://prove2.me/submissions/97d45184-b05a-448d-bd66-348115df5098

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1) ≥ 0 := by
  intros
  have p2m_pos_a : (0 : ℝ) < a := by grind
  have p2m_pos_b : (0 : ℝ) < b := by grind
  have p2m_pos_c : (0 : ℝ) < c := by grind
  
  have p2m_cond_3 : (c : ℝ) < (a + b) := by first | assumption | aesop | linarith
  have p2m_cond_3_gap : (0 : ℝ) ≤ (a + b) - (c) := by linarith only [p2m_cond_3]
  have p2m_cond_4 : (a : ℝ) < (b + c) := by first | assumption | aesop | linarith
  have p2m_cond_4_gap : (0 : ℝ) ≤ (b + c) - (a) := by linarith only [p2m_cond_4]
  have p2m_cond_5 : (b : ℝ) < (a + c) := by first | assumption | aesop | linarith
  have p2m_cond_5_gap : (0 : ℝ) ≤ (a + c) - (b) := by linarith only [p2m_cond_5]
  have h_identity : (((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((b ^ 3) * (c ^ 2)) + ((-1) * a * b * (c ^ 3)) + ((-1) * a * c * (b ^ 3)) + ((-1) * b * c * (a ^ 3))) = ((1 / 2) : ℝ) * ((a + b) - (c)) * (((a * b) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * ((b + c) - (a)) * (((a * c) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * ((a + c) - (b)) * (((a * b) + ((-1) * a * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((b ^ 3) * (c ^ 2)) + ((-1) * a * b * (c ^ 3)) + ((-1) * a * c * (b ^ 3)) + ((-1) * b * c * (a ^ 3))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c) := by positivity
  have h_rational : (a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1)) - (0) = ((((a ^ 2) * (c ^ 3)) + ((a ^ 3) * (b ^ 2)) + ((b ^ 3) * (c ^ 2)) + ((-1) * a * b * (c ^ 3)) + ((-1) * a * c * (b ^ 3)) + ((-1) * b * c * (a ^ 3)))) / ((a * b * c)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
