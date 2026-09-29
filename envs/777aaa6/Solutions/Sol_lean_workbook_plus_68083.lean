-- Prove2me | solution 1 for lean_workbook_plus_68083
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:01.849887+00:00
-- url     : https://prove2.me/submissions/e51820a7-1761-44f3-b64a-b55f397d414c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x) : (x / (4 + x ^ 2) ≤ (1 / 20) * (1 + 15 / (1 + x))) := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (64 + (x ^ 3) + ((-16) * x) + ((-4) * (x ^ 2))) = (64 : ℝ) * 1 * ((1 + ((-1 / 4) * x)))^2 + (16 : ℝ) * ((x) - (0)) * ((1 + ((-1 / 4) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (64 + (x ^ 3) + ((-16) * x) + ((-4) * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (20 * (1 + x) * (4 + (x ^ 2))) := by positivity
  have h_rational : ((1 / 20) * (1 + 15 / (1 + x))) - (x / (4 + x ^ 2)) = ((64 + (x ^ 3) + ((-16) * x) + ((-4) * (x ^ 2)))) / ((20 * (1 + x) * (4 + (x ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
