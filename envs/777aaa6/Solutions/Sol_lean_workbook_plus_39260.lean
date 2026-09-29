-- Prove2me | solution 1 for lean_workbook_plus_39260
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:18.720962+00:00
-- url     : https://prove2.me/submissions/d2d803f5-dcbf-4d2d-918a-7ac4fb983809

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) : (1 / (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + 1 / (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + 1 / (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2) ≥ 4 / (3 * (a ^ 2 + b ^ 2 + c ^ 2))) := by
  intros
  have p2m_cond_0 : (a + b + c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0) - (a + b + c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((9 * (a ^ 6)) + (9 * (b ^ 6)) + (9 * (c ^ 6)) + ((-9) * (a ^ 2) * (b ^ 4)) + ((-9) * (a ^ 2) * (c ^ 4)) + ((-9) * (a ^ 4) * (b ^ 2)) + ((-9) * (a ^ 4) * (c ^ 2)) + ((-9) * (b ^ 2) * (c ^ 4)) + ((-9) * (b ^ 4) * (c ^ 2)) + ((-22) * (a ^ 2) * (b ^ 2) * (c ^ 2))) = (32 : ℝ) * 1 * ((a * b * c))^2 := by
    linear_combination ((((-9) * (a ^ 5)) + ((-9) * (b ^ 5)) + ((-9) * (c ^ 5)) + (9 * a * (b ^ 4)) + (9 * a * (c ^ 4)) + (9 * b * (a ^ 4)) + (9 * b * (c ^ 4)) + (9 * c * (a ^ 4)) + (9 * c * (b ^ 4)) + ((-18) * a * b * (c ^ 3)) + ((-18) * a * c * (b ^ 3)) + ((-18) * b * c * (a ^ 3)) + (18 * a * (b ^ 2) * (c ^ 2)) + (18 * b * (a ^ 2) * (c ^ 2)) + (18 * c * (a ^ 2) * (b ^ 2)))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((9 * (a ^ 6)) + (9 * (b ^ 6)) + (9 * (c ^ 6)) + ((-9) * (a ^ 2) * (b ^ 4)) + ((-9) * (a ^ 2) * (c ^ 4)) + ((-9) * (a ^ 4) * (b ^ 2)) + ((-9) * (a ^ 4) * (c ^ 2)) + ((-9) * (b ^ 2) * (c ^ 4)) + ((-9) * (b ^ 4) * (c ^ 2)) + ((-22) * (a ^ 2) * (b ^ 2) * (c ^ 2))) := by
    rw [h_identity]
    positivity
  have h_denominator : (0 : ℝ) < (3 * ((a ^ 2) + (b ^ 2) + (c ^ 2)) * ((a ^ 2) + (3 * (b ^ 2)) + (3 * (c ^ 2))) * ((b ^ 2) + (3 * (a ^ 2)) + (3 * (c ^ 2))) * ((c ^ 2) + (3 * (a ^ 2)) + (3 * (b ^ 2)))) := by positivity
  have h_rational : (1 / (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + 1 / (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + 1 / (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2)) - (4 / (3 * (a ^ 2 + b ^ 2 + c ^ 2))) = (((9 * (a ^ 6)) + (9 * (b ^ 6)) + (9 * (c ^ 6)) + ((-9) * (a ^ 2) * (b ^ 4)) + ((-9) * (a ^ 2) * (c ^ 4)) + ((-9) * (a ^ 4) * (b ^ 2)) + ((-9) * (a ^ 4) * (c ^ 2)) + ((-9) * (b ^ 2) * (c ^ 4)) + ((-9) * (b ^ 4) * (c ^ 2)) + ((-22) * (a ^ 2) * (b ^ 2) * (c ^ 2)))) / ((3 * ((a ^ 2) + (b ^ 2) + (c ^ 2)) * ((a ^ 2) + (3 * (b ^ 2)) + (3 * (c ^ 2))) * ((b ^ 2) + (3 * (a ^ 2)) + (3 * (c ^ 2))) * ((c ^ 2) + (3 * (a ^ 2)) + (3 * (b ^ 2))))) := by
    field_simp (disch := first | positivity | linarith | aesop)
    <;> ring
  apply sub_nonneg.mp
  rw [h_rational]
  exact div_nonneg h_nonnegative (le_of_lt h_denominator)
