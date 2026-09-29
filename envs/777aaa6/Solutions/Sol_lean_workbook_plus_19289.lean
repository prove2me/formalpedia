-- Prove2me | solution 1 for lean_workbook_plus_19289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:05:26.617841+00:00
-- url     : https://prove2.me/submissions/5971915c-a492-4ab5-9eb6-fed015148fe0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2) * (a^2 + b^2 + c^2)^2 / 3)   := by
  have hS : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hCS : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2) := by
    nlinarith [sq_nonneg (a * (b * c) - b * (a * b)), sq_nonneg (a * (c * a) - c * (a * b)), sq_nonneg (b * (c * a) - c * (b * c))]
  have hQ : 3 * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
  have hbound : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 / 3 := by
    have hmul := mul_le_mul_of_nonneg_left hQ hS
    nlinarith
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt hbound)
