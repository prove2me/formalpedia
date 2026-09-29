-- Prove2me | solution 1 for lean_workbook_plus_18507
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:04:19.849809+00:00
-- url     : https://prove2.me/submissions/a92b5ff2-4f2d-4c19-a7ed-23166dfbfe4a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 9 / (3 * a + 2 * b + c) ≤ 2 / (a + b) + 1 / (a + c) := by
  intro a b c
  intros
  have ha0 : 0 < a := by aesop
  have hb0 : 0 < b := by aesop
  have hc0 : 0 < c := by aesop
  
  have h_identity : ((2 * (b ^ 2)) + (2 * (c ^ 2)) + ((-4) * b * c)) = (2 : ℝ) * 1 * ((b + ((-1) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((2 * (b ^ 2)) + (2 * (c ^ 2)) + ((-4) * b * c)) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < ((a + b) * (a + c) * (c + (2 * b) + (3 * a))) := by first | positivity | nlinarith | aesop
  have h_rational : (2 / (a + b) + 1 / (a + c)) - (9 / (3 * a + 2 * b + c)) = (((2 * (b ^ 2)) + (2 * (c ^ 2)) + ((-4) * b * c))) / (((a + b) * (a + c) * (c + (2 * b) + (3 * a)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
