-- Prove2me | solution 1 for lean_workbook_plus_32437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:32.949781+00:00
-- url     : https://prove2.me/submissions/6b4ad462-12a7-4b19-a911-09fce758c15a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) ^ 4 / (a ^ 2 * b ^ 2) + (b - c) ^ 4 / (b ^ 2 * c ^ 2) + (c - a) ^ 4 / (c ^ 2 * a ^ 2) ≥ 1 / 2 * ((a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a)) ^ 2 := by
  intros
  
  have h_identity : (((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-2) * (a ^ 3) * (b ^ 3)) + ((-2) * (a ^ 3) * (c ^ 3)) + ((-2) * (b ^ 3) * (c ^ 3)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * (c ^ 4)) + ((-2) * a * c * (b ^ 4)) + ((-2) * b * c * (a ^ 4)) + (2 * a * (b ^ 2) * (c ^ 3)) + (2 * a * (b ^ 3) * (c ^ 2)) + (2 * b * (a ^ 2) * (c ^ 3)) + (2 * b * (a ^ 3) * (c ^ 2)) + (2 * c * (a ^ 2) * (b ^ 3)) + (2 * c * (a ^ 3) * (b ^ 2))) = (1 : ℝ) * 1 * (((a * (c ^ 2)) + (b * (a ^ 2)) + (c * (b ^ 2)) + ((-1) * a * (b ^ 2)) + ((-1) * b * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-2) * (a ^ 3) * (b ^ 3)) + ((-2) * (a ^ 3) * (c ^ 3)) + ((-2) * (b ^ 3) * (c ^ 3)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * (c ^ 4)) + ((-2) * a * c * (b ^ 4)) + ((-2) * b * c * (a ^ 4)) + (2 * a * (b ^ 2) * (c ^ 3)) + (2 * a * (b ^ 3) * (c ^ 2)) + (2 * b * (a ^ 2) * (c ^ 3)) + (2 * b * (a ^ 3) * (c ^ 2)) + (2 * c * (a ^ 2) * (b ^ 3)) + (2 * c * (a ^ 3) * (b ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (2 * (a ^ 2) * (b ^ 2) * (c ^ 2)) := by positivity
  have h_rational : ((a - b) ^ 4 / (a ^ 2 * b ^ 2) + (b - c) ^ 4 / (b ^ 2 * c ^ 2) + (c - a) ^ 4 / (c ^ 2 * a ^ 2)) - (1 / 2 * ((a - b) ^ 2 / (a * b) + (b - c) ^ 2 / (b * c) + (c - a) ^ 2 / (c * a)) ^ 2) = ((((a ^ 2) * (b ^ 4)) + ((a ^ 2) * (c ^ 4)) + ((a ^ 4) * (b ^ 2)) + ((a ^ 4) * (c ^ 2)) + ((b ^ 2) * (c ^ 4)) + ((b ^ 4) * (c ^ 2)) + ((-2) * (a ^ 3) * (b ^ 3)) + ((-2) * (a ^ 3) * (c ^ 3)) + ((-2) * (b ^ 3) * (c ^ 3)) + ((-6) * (a ^ 2) * (b ^ 2) * (c ^ 2)) + ((-2) * a * b * (c ^ 4)) + ((-2) * a * c * (b ^ 4)) + ((-2) * b * c * (a ^ 4)) + (2 * a * (b ^ 2) * (c ^ 3)) + (2 * a * (b ^ 3) * (c ^ 2)) + (2 * b * (a ^ 2) * (c ^ 3)) + (2 * b * (a ^ 3) * (c ^ 2)) + (2 * c * (a ^ 2) * (b ^ 3)) + (2 * c * (a ^ 3) * (b ^ 2)))) / ((2 * (a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
