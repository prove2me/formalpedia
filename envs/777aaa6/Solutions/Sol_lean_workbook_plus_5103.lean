-- Prove2me | solution 1 for lean_workbook_plus_5103
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:09:01.405755+00:00
-- url     : https://prove2.me/submissions/6459eecd-b226-44d4-bf41-78a211114bfc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → 1 / (x ^ 2 - 4 * x + 9) ≤ (x + 2) / 18 := by
  intro x
  intros
  have hpoly : 0 < 9+x^2+(-4)*x := by nlinarith [sq_nonneg (x-2)]
  have p2m_cond_0 : (0 : ℝ) ≤ (x) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0 : ℝ) ≤ (x) - (0) := by linarith only [p2m_cond_0]
  have h_identity : (x + (x ^ 3) + ((-2) * (x ^ 2))) = (1 : ℝ) * ((x) - (0)) * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (x + (x ^ 3) + ((-2) * (x ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (18 * (9 + (x ^ 2) + ((-4) * x))) := by first | positivity | nlinarith | aesop
  have h_rational : ((x + 2) / 18) - (1 / (x ^ 2 - 4 * x + 9)) = ((x + (x ^ 3) + ((-2) * (x ^ 2)))) / ((18 * (9 + (x ^ 2) + ((-4) * x)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
