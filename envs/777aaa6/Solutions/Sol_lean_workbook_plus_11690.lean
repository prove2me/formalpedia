-- Prove2me | solution 1 for lean_workbook_plus_11690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:32.849587+00:00
-- url     : https://prove2.me/submissions/76057c4c-4ffb-4fbe-97dc-3b58a9b12360

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  a / (a^4 + b^2) + b / (a^2 + b^4) ≤ 1 / (a * b) := by
  have ha0 : 0 < a := h₀.1
  have hb0 : 0 < b := h₀.2
  intros
  
  have h_identity : ((a ^ 6) + (b ^ 6) + ((a ^ 2) * (b ^ 2)) + ((a ^ 4) * (b ^ 4)) + ((-1) * a * (b ^ 4)) + ((-1) * b * (a ^ 4)) + ((-1) * (a ^ 2) * (b ^ 5)) + ((-1) * (a ^ 5) * (b ^ 2))) = (1 : ℝ) * 1 * ((((-1 / 2) * (a ^ 3)) + ((-1 / 2) * (b ^ 3)) + ((a ^ 2) * (b ^ 2))))^2 + ((3 / 4) : ℝ) * 1 * (((a ^ 3) + ((-1 / 3) * (b ^ 3)) + ((-2 / 3) * a * b)))^2 + ((2 / 3) : ℝ) * 1 * ((((-1) * (b ^ 3)) + (a * b)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ ((a ^ 6) + (b ^ 6) + ((a ^ 2) * (b ^ 2)) + ((a ^ 4) * (b ^ 4)) + ((-1) * a * (b ^ 4)) + ((-1) * b * (a ^ 4)) + ((-1) * (a ^ 2) * (b ^ 5)) + ((-1) * (a ^ 5) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (a * b * ((a ^ 2) + (b ^ 4)) * ((a ^ 4) + (b ^ 2))) := by positivity
  have h_rational : (1 / (a * b)) - (a / (a^4 + b^2) + b / (a^2 + b^4)) = (((a ^ 6) + (b ^ 6) + ((a ^ 2) * (b ^ 2)) + ((a ^ 4) * (b ^ 4)) + ((-1) * a * (b ^ 4)) + ((-1) * b * (a ^ 4)) + ((-1) * (a ^ 2) * (b ^ 5)) + ((-1) * (a ^ 5) * (b ^ 2)))) / ((a * b * ((a ^ 2) + (b ^ 4)) * ((a ^ 4) + (b ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
