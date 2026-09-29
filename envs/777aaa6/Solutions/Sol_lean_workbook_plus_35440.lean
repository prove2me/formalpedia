-- Prove2me | solution 1 for lean_workbook_plus_35440
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:53.478868+00:00
-- url     : https://prove2.me/submissions/09ec32e1-f951-4c18-a49a-3811698c6181

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (u : ℝ) (h : u > 0) : u + (1 / u) ≥ 2 := by
  intros
  
  have h_identity : (1 + (u ^ 2) + ((-2) * u)) = (1 : ℝ) * 1 * ((1 + ((-1) * u)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (u ^ 2) + ((-2) * u)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < u := by positivity
  have h_rational : (u + (1 / u)) - (2) = ((1 + (u ^ 2) + ((-2) * u))) / (u) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
