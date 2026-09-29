-- Prove2me | solution 1 for lean_workbook_plus_1424
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:36.508224+00:00
-- url     : https://prove2.me/submissions/d4500ee0-da87-47e1-a566-1a93942a983e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c > 0) (hcd : c * d * b > 0) (habd : a * b * d > 0) : (a^2 + b^2 ≥ c^2 + d^2) → b / (a + c) + a / (b + d) ≥ 1 := by
  clear habc hcd habd
  intros
  have p2m_cond_7 : (c^2 + d^2 : ℝ) ≤ (a^2 + b^2) := by first | assumption | aesop | linarith
  have p2m_cond_7_gap : (0 : ℝ) ≤ (a^2 + b^2) - (c^2 + d^2) := by linarith only [p2m_cond_7]
  have h_identity : ((a ^ 2) + (b ^ 2) + (a * c) + (b * d) + ((-1) * a * b) + ((-1) * a * d) + ((-1) * b * c) + ((-1) * c * d)) = ((1 / 2) : ℝ) * 1 * ((a + c + ((-1) * b) + ((-1) * d)))^2 + ((1 / 2) : ℝ) * ((a^2 + b^2) - (c^2 + d^2)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 2) + (b ^ 2) + (a * c) + (b * d) + ((-1) * a * b) + ((-1) * a * d) + ((-1) * b * c) + ((-1) * c * d)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + c) * (b + d)) := by positivity
  have h_rational : (b / (a + c) + a / (b + d)) - (1) = (((a ^ 2) + (b ^ 2) + (a * c) + (b * d) + ((-1) * a * b) + ((-1) * a * d) + ((-1) * b * c) + ((-1) * c * d))) / (((a + c) * (b + d))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
