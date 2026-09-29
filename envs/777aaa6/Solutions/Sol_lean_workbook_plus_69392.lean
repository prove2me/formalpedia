-- Prove2me | solution 1 for lean_workbook_plus_69392
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:06:37.357535+00:00
-- url     : https://prove2.me/submissions/3dba829a-661e-405a-a6b8-684cf9695278

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  1 / 9 * (a^2 + b^2 + c^2) ≥ 1 / (1 / a^2 + 1 / b^2 + 1 / c^2) := by
  intros
  have ha0 : 0 < a := by aesop
  have hb0 : 0 < b := by aesop
  have hc0 : 0 < c := by aesop
  
  have h_identity : (((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2))) = (1 : ℝ) * 1 * (((b * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + (1 : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * c * (b ^ 2))))^2 + (1 : ℝ) * 1 * (((a * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (9 * (((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (c ^ 2)) + ((b ^ 2) * (c ^ 2)))) := by first | positivity | nlinarith | aesop
  have h_rational : (1 / 9 * (a^2 + b^2 + c^2)) - (1 / (1 / a^2 + 1 / b^2 + 1 / c^2)) = ((((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2)))) / ((9 * (((a ^ 2) * (b ^ 2)) + ((a ^ 2) * (c ^ 2)) + ((b ^ 2) * (c ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
