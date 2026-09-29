-- Prove2me | solution 1 for lean_workbook_plus_5966
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:32.00625+00:00
-- url     : https://prove2.me/submissions/87c43a7d-b9b9-45c0-9a48-c715b7a45c32

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (s : ℝ) (hs : s > 0) : (s^3 + 2) / (3 * s) ≥ 1 := by
  intros
  have p2m_cond_0 : (0 : ℝ) < (s) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (s) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (2 + (s ^ 3) + ((-3) * s)) = (2 : ℝ) * 1 * ((1 + ((-1) * s)))^2 + (1 : ℝ) * ((s) - (0)) * ((1 + ((-1) * s)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (2 + (s ^ 3) + ((-3) * s)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (3 * s) := by positivity
  have h_rational : ((s^3 + 2) / (3 * s)) - (1) = ((2 + (s ^ 3) + ((-3) * s))) / ((3 * s)) := by
    field_simp (disch := positivity)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
