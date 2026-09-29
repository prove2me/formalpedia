-- Prove2me | solution 1 for lean_workbook_plus_43757
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:33.69885+00:00
-- url     : https://prove2.me/submissions/ba73eb8f-3787-47c7-84b6-2b85b4c4172f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) * (1 / (b + d) + 1 / (a + c)) ≥ 4 * (a + b) / (a + b + c + d) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (a) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (a) - (0) := by linarith only [p2m_cond_0]
  have p2m_cond_1 : (0 : ℝ) < (b) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (b) - (0) := by linarith only [p2m_cond_1]
  have h_identity : ((a ^ 3) + (b ^ 3) + (a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + ((-2) * c * (b ^ 2)) + ((-2) * d * (a ^ 2)) + (2 * c * (a ^ 2)) + (2 * d * (b ^ 2)) + ((-2) * a * c * d) + ((-2) * b * c * d)) = (1 : ℝ) * ((a) - (0)) * ((a + c + ((-1) * b) + ((-1) * d)))^2 + (1 : ℝ) * ((b) - (0)) * ((a + c + ((-1) * b) + ((-1) * d)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 3) + (b ^ 3) + (a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + ((-2) * c * (b ^ 2)) + ((-2) * d * (a ^ 2)) + (2 * c * (a ^ 2)) + (2 * d * (b ^ 2)) + ((-2) * a * c * d) + ((-2) * b * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + c) * (b + d) * (a + b + c + d)) := by positivity
  have h_rational : ((a + b) * (1 / (b + d) + 1 / (a + c))) - (4 * (a + b) / (a + b + c + d)) = (((a ^ 3) + (b ^ 3) + (a * (c ^ 2)) + (a * (d ^ 2)) + (b * (c ^ 2)) + (b * (d ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (a ^ 2)) + ((-2) * c * (b ^ 2)) + ((-2) * d * (a ^ 2)) + (2 * c * (a ^ 2)) + (2 * d * (b ^ 2)) + ((-2) * a * c * d) + ((-2) * b * c * d))) / (((a + c) * (b + d) * (a + b + c + d))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
