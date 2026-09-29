-- Prove2me | solution 1 for lean_workbook_plus_4771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:40.877012+00:00
-- url     : https://prove2.me/submissions/53ddce52-9e1f-472e-b6e5-ed29cf218ec3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 3 * (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((2 * (a ^ 2) * (c ^ 3)) + (2 * (a ^ 3) * (b ^ 2)) + (2 * (b ^ 3) * (c ^ 2)) + (4 * (a ^ 2) * (b ^ 3)) + (4 * (a ^ 3) * (c ^ 2)) + (4 * (b ^ 2) * (c ^ 3)) + ((-6) * a * (b ^ 2) * (c ^ 2)) + ((-6) * b * (a ^ 2) * (c ^ 2)) + ((-6) * c * (a ^ 2) * (b ^ 2))) = (2 : ℝ) * ((a) - (0)) * (((a * b) + ((-1) * b * c)))^2 + (4 : ℝ) * ((a) - (0)) * (((a * c) + ((-1) * b * c)))^2 + (4 : ℝ) * ((b) - (0)) * (((a * b) + ((-1) * a * c)))^2 + (2 : ℝ) * ((b) - (0)) * (((a * c) + ((-1) * b * c)))^2 + (2 : ℝ) * ((c) - (0)) * (((a * b) + ((-1) * a * c)))^2 + (4 : ℝ) * ((c) - (0)) * (((a * b) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (a ^ 2) * (c ^ 3)) + (2 * (a ^ 3) * (b ^ 2)) + (2 * (b ^ 3) * (c ^ 2)) + (4 * (a ^ 2) * (b ^ 3)) + (4 * (a ^ 3) * (c ^ 2)) + (4 * (b ^ 2) * (c ^ 3)) + ((-6) * a * (b ^ 2) * (c ^ 2)) + ((-6) * b * (a ^ 2) * (c ^ 2)) + ((-6) * c * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c * (a + (2 * b)) * (b + (2 * c)) * (c + (2 * a))) := by positivity
  have h_rational : (1 / a + 1 / b + 1 / c) - (3 * (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a))) = (((2 * (a ^ 2) * (c ^ 3)) + (2 * (a ^ 3) * (b ^ 2)) + (2 * (b ^ 3) * (c ^ 2)) + (4 * (a ^ 2) * (b ^ 3)) + (4 * (a ^ 3) * (c ^ 2)) + (4 * (b ^ 2) * (c ^ 3)) + ((-6) * a * (b ^ 2) * (c ^ 2)) + ((-6) * b * (a ^ 2) * (c ^ 2)) + ((-6) * c * (a ^ 2) * (b ^ 2)))) / ((a * b * c * (a + (2 * b)) * (b + (2 * c)) * (c + (2 * a)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
