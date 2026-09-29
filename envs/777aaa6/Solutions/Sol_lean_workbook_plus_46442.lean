-- Prove2me | solution 1 for lean_workbook_plus_46442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:05:51.523314+00:00
-- url     : https://prove2.me/submissions/c9ad63af-d4a4-4653-afdd-156092b53aad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : x ≥ -1/3) : x / (x ^ 2 + 1) ≤ 1 / 2 := by
  intros
  
  have h_identity : (1 + (x ^ 2) + ((-2) * x)) = (1 : ℝ) * 1 * ((1 + ((-1) * x)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (1 + (x ^ 2) + ((-2) * x)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (1 + (x ^ 2))) := by positivity
  have h_rational : (1 / 2) - (x / (x ^ 2 + 1)) = ((1 + (x ^ 2) + ((-2) * x))) / ((2 * (1 + (x ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
