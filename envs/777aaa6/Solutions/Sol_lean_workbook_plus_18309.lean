-- Prove2me | solution 1 for lean_workbook_plus_18309
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:13.879481+00:00
-- url     : https://prove2.me/submissions/808804e0-3888-4bf4-af7c-1a451877ac72

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / b + 4 * b / a + a * b / (a ^ 2 + 4 * b ^ 2) ≥ 17 / 4 := by
  intros
  
  have h_identity : ((4 * (a ^ 4)) + (64 * (b ^ 4)) + ((-68) * a * (b ^ 3)) + ((-17) * b * (a ^ 3)) + (36 * (a ^ 2) * (b ^ 2))) = (4 : ℝ) * 1 * (((a ^ 2) + ((1 / 4) * (b ^ 2)) + ((-17 / 8) * a * b)))^2 + ((255 / 16) : ℝ) * 1 * ((((-2) * (b ^ 2)) + (a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((4 * (a ^ 4)) + (64 * (b ^ 4)) + ((-68) * a * (b ^ 3)) + ((-17) * b * (a ^ 3)) + (36 * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (4 * a * b * ((a ^ 2) + (4 * (b ^ 2)))) := by positivity
  have h_rational : (a / b + 4 * b / a + a * b / (a ^ 2 + 4 * b ^ 2)) - (17 / 4) = (((4 * (a ^ 4)) + (64 * (b ^ 4)) + ((-68) * a * (b ^ 3)) + ((-17) * b * (a ^ 3)) + (36 * (a ^ 2) * (b ^ 2)))) / ((4 * a * b * ((a ^ 2) + (4 * (b ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
