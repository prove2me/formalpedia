-- Prove2me | solution 1 for lean_workbook_plus_51722
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:08:14.003624+00:00
-- url     : https://prove2.me/submissions/00d97653-1553-403b-88e5-6b7608ada97a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b w u : ℝ) (ha : 0 < a) (hb : 0 < b) (hw : 0 < w) (hu : 0 < u) : (a * b) / (a + b) ≤ (w^2 * a + u^2 * b) / (w + u)^2 := by
  intros
  
  have h_identity : (((a ^ 2) * (w ^ 2)) + ((b ^ 2) * (u ^ 2)) + ((-2) * a * b * u * w)) = (1 : ℝ) * 1 * (((a * w) + ((-1) * b * u)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (w ^ 2)) + ((b ^ 2) * (u ^ 2)) + ((-2) * a * b * u * w)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (((u + w) ^ 2) * (a + b)) := by positivity
  have h_rational : ((w^2 * a + u^2 * b) / (w + u)^2) - ((a * b) / (a + b)) = ((((a ^ 2) * (w ^ 2)) + ((b ^ 2) * (u ^ 2)) + ((-2) * a * b * u * w))) / ((((u + w) ^ 2) * (a + b))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
