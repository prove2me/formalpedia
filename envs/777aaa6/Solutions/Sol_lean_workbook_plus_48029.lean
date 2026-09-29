-- Prove2me | solution 1 for lean_workbook_plus_48029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:35.657735+00:00
-- url     : https://prove2.me/submissions/a300a12b-23f8-4992-aa22-0ebea66ed271

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (hab : 0 < a ∧ 0 < b) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / (a ^ 2 - a * b + b ^ 2) ≥ 3 / (a * b) := by
  intros
  have ha : 0 < a := hab.1
  have hb : 0 < b := hab.2
  have hq : 0 < a^2 + b^2 + (-1)*a*b := by nlinarith [sq_nonneg (a-b), sq_pos_of_pos ha]
  have hq2 : 0 < a^2-a*b+b^2 := by nlinarith [hq]
  
  have h_identity : ((a ^ 4) + (b ^ 4) + ((-4) * a * (b ^ 3)) + ((-4) * b * (a ^ 3)) + (6 * (a ^ 2) * (b ^ 2))) = (1 : ℝ) * 1 * (((a ^ 2) + (b ^ 2) + ((-2) * a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 4) + (b ^ 4) + ((-4) * a * (b ^ 3)) + ((-4) * b * (a ^ 3)) + (6 * (a ^ 2) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a ^ 2) * (b ^ 2) * ((a ^ 2) + (b ^ 2) + ((-1) * a * b))) := by positivity
  have h_rational : (1 / a ^ 2 + 1 / b ^ 2 + 1 / (a ^ 2 - a * b + b ^ 2)) - (3 / (a * b)) = (((a ^ 4) + (b ^ 4) + ((-4) * a * (b ^ 3)) + ((-4) * b * (a ^ 3)) + (6 * (a ^ 2) * (b ^ 2)))) / (((a ^ 2) * (b ^ 2) * ((a ^ 2) + (b ^ 2) + ((-1) * a * b)))) := by
    field_simp (disch := first | positivity | nlinarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
