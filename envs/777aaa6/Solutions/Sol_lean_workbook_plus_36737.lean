-- Prove2me | solution 1 for lean_workbook_plus_36737
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:13.954445+00:00
-- url     : https://prove2.me/submissions/88425780-10dc-48ce-aae9-2491b0199b1a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y z u : ℝ)
  (h₀ : 0 < u)
  (h₁ : u = y + z)
  (h₂ : 1 ≤ x * u + u^2 / 4) :
  x ≥ (4 - u^2) / (4 * u) := by
  intros
  have p2m_cond_2 : (1 : ℝ) ≤ (x * u + u^2 / 4) := by first | assumption | aesop | linarith
  have p2m_cond_2_gap : (0 : ℝ) ≤ (x * u + u^2 / 4) - (1) := by linarith only [p2m_cond_2]
  have h_identity : ((-4) + (u ^ 2) + (4 * u * x)) = (4 : ℝ) * ((x * u + u^2 / 4) - (1)) * (1)^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((-4) + (u ^ 2) + (4 * u * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * u) := by positivity
  have h_rational : (x) - ((4 - u^2) / (4 * u)) = (((-4) + (u ^ 2) + (4 * u * x))) / ((4 * u)) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
