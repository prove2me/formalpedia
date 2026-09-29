-- Prove2me | solution 1 for lean_workbook_plus_22674
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:28.247006+00:00
-- url     : https://prove2.me/submissions/fd212b9c-a55a-4767-80af-db50e7da8cfb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) (hx : 0 < x) : (x^4 + 3) / (x + 2) ≥ 8 / 9 * x + 4 / 9 := by
  intros
  
  have h_identity : (19 + ((-20) * x) + ((-8) * (x ^ 2)) + (9 * (x ^ 4))) = (10 : ℝ) * 1 * ((1 + ((-1) * x)))^2 + (9 : ℝ) * 1 * ((1 + ((-1) * (x ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (19 + ((-20) * x) + ((-8) * (x ^ 2)) + (9 * (x ^ 4))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (9 * (2 + x)) := by positivity
  have h_rational : ((x^4 + 3) / (x + 2)) - (8 / 9 * x + 4 / 9) = ((19 + ((-20) * x) + ((-8) * (x ^ 2)) + (9 * (x ^ 4)))) / ((9 * (2 + x))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
