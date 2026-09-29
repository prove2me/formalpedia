-- Prove2me | solution 1 for lean_workbook_plus_7738
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:38.819499+00:00
-- url     : https://prove2.me/submissions/52e7ed5c-8c31-4a91-8d91-460f812e620f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b ^ 2 + b / c ^ 2 + c / a ^ 2) ≥ (1 / a + 1 / b + 1 / c) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : (((a ^ 2) * (b ^ 3)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 2)) + ((-1) * c * (a ^ 2) * (b ^ 2))) = (1 : ℝ) * ((a) - (0)) * (((a * c) + ((-1) * b * c)))^2 + (1 : ℝ) * ((b) - (0)) * (((a * b) + ((-1) * a * c)))^2 + (1 : ℝ) * ((c) - (0)) * (((a * b) + ((-1) * b * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 3)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 2)) + ((-1) * c * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a ^ 2) * (b ^ 2) * (c ^ 2)) := by positivity
  have h_rational : ((a / b ^ 2 + b / c ^ 2 + c / a ^ 2)) - ((1 / a + 1 / b + 1 / c)) = ((((a ^ 2) * (b ^ 3)) + ((a ^ 3) * (c ^ 2)) + ((b ^ 2) * (c ^ 3)) + ((-1) * a * (b ^ 2) * (c ^ 2)) + ((-1) * b * (a ^ 2) * (c ^ 2)) + ((-1) * c * (a ^ 2) * (b ^ 2)))) / (((a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
