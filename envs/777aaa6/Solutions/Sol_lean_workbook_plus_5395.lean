-- Prove2me | solution 1 for lean_workbook_plus_5395
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:19.709167+00:00
-- url     : https://prove2.me/submissions/608af47e-af8f-4d59-9385-c6a7f2e1250d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1) :
  (1 - x) ^ 3 / (1 + 2 * x) ≥ 116 / 225 - 76 * x / 75 := by
  intros
  have p2m_cond_1 : (x : ℝ) < (1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (1) - (x) := by linarith only [p2m_cond_1]
  have h_identity : (109 + ((-679) * x) + ((-225) * (x ^ 3)) + (1131 * (x ^ 2))) = (84 : ℝ) * 1 * ((1 + ((-3) * x)))^2 + (25 : ℝ) * ((1) - (x)) * ((1 + ((-3) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (109 + ((-679) * x) + ((-225) * (x ^ 3)) + (1131 * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (225 * (1 + (2 * x))) := by positivity
  have h_rational : ((1 - x) ^ 3 / (1 + 2 * x)) - (116 / 225 - 76 * x / 75) = ((109 + ((-679) * x) + ((-225) * (x ^ 3)) + (1131 * (x ^ 2)))) / ((225 * (1 + (2 * x)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
