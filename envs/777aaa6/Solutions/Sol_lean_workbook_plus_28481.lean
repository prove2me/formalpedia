-- Prove2me | solution 1 for lean_workbook_plus_28481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:57.972321+00:00
-- url     : https://prove2.me/submissions/6d052143-d4a5-42f6-bcba-14e254678904

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a * b / (a ^ 2 + 4 * b ^ 2) + b ^ 2 / (3 * a ^ 2 + 2 * b ^ 2)) ≤ 3 / 5 := by
  intros
  
  have h_identity : ((4 * (b ^ 4)) + (9 * (a ^ 4)) + ((-30) * b * (a ^ 3)) + ((-20) * a * (b ^ 3)) + (37 * (a ^ 2) * (b ^ 2))) = (9 : ℝ) * 1 * (((a ^ 2) + ((2 / 3) * (b ^ 2)) + ((-5 / 3) * a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((4 * (b ^ 4)) + (9 * (a ^ 4)) + ((-30) * b * (a ^ 3)) + ((-20) * a * (b ^ 3)) + (37 * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (5 * ((a ^ 2) + (4 * (b ^ 2))) * ((2 * (b ^ 2)) + (3 * (a ^ 2)))) := by positivity
  have h_rational : (3 / 5) - ((2 * a * b / (a ^ 2 + 4 * b ^ 2) + b ^ 2 / (3 * a ^ 2 + 2 * b ^ 2))) = (((4 * (b ^ 4)) + (9 * (a ^ 4)) + ((-30) * b * (a ^ 3)) + ((-20) * a * (b ^ 3)) + (37 * (a ^ 2) * (b ^ 2)))) / ((5 * ((a ^ 2) + (4 * (b ^ 2))) * ((2 * (b ^ 2)) + (3 * (a ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
