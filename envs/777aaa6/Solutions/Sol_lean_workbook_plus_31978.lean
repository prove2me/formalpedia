-- Prove2me | solution 1 for lean_workbook_plus_31978
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:04.77508+00:00
-- url     : https://prove2.me/submissions/3cf75a7a-1dff-4b6f-bef2-b9ba44e5617b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≥ 9 / (a * b + b * c + c * a) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have p2m_cond_2 : (0 : ℝ) < (c) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (c) - (0) := by linarith only [p2m_cond_2]
  have h_identity : ((a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-6) * a * b * c)) = (1 : ℝ) * ((a) - (0)) * ((b + ((-1) * c)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + ((-1) * c)))^2 + (1 : ℝ) * ((c) - (0)) * ((a + ((-1) * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-6) * a * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * c * ((a * b) + (a * c) + (b * c))) := by positivity
  have h_rational : ((1 / (a * b) + 1 / (b * c) + 1 / (c * a))) - (9 / (a * b + b * c + c * a)) = (((a * (b ^ 2)) + (a * (c ^ 2)) + (b * (a ^ 2)) + (b * (c ^ 2)) + (c * (a ^ 2)) + (c * (b ^ 2)) + ((-6) * a * b * c))) / ((a * b * c * ((a * b) + (a * c) + (b * c)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
