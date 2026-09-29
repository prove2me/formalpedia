-- Prove2me | solution 1 for lean_workbook_plus_23983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:56.30885+00:00
-- url     : https://prove2.me/submissions/557e5cf4-6284-4fbf-bd49-df91466166cd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / 9 - a / (a + 2) ^ 2 ≥ 1 / (9 * (a ^ 2 + a + 1)) - 1 / 27 := by
  intros
  
  have h_identity : (4 + ((-7) * a) + ((-7) * (a ^ 3)) + (4 * (a ^ 4)) + (6 * (a ^ 2))) = ((7 / 2) : ℝ) * 1 * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * 1 * ((1 + ((-1) * (a ^ 2))))^2 + ((7 / 2) : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (4 + ((-7) * a) + ((-7) * (a ^ 3)) + (4 * (a ^ 4)) + (6 * (a ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (27 * ((2 + a) ^ 2) * (1 + a + (a ^ 2))) := by positivity
  have h_rational : (1 / 9 - a / (a + 2) ^ 2) - (1 / (9 * (a ^ 2 + a + 1)) - 1 / 27) = ((4 + ((-7) * a) + ((-7) * (a ^ 3)) + (4 * (a ^ 4)) + (6 * (a ^ 2)))) / ((27 * ((2 + a) ^ 2) * (1 + a + (a ^ 2)))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
