-- Prove2me | solution 1 for lean_workbook_plus_79828
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:27.249487+00:00
-- url     : https://prove2.me/submissions/c3a5b831-2490-4188-95a5-dbd82ebe191f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (hab : a ≥ 1) (hbc : b ≥ 1) (hca : c ≥ 1) :
    a * b ^ 2 + b * c ^ 2 + c * a ^ 2 + 6 ≥ 3 * (a + b + c) := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ b ^ 2 - 1 by nlinarith)
  have h₂ := mul_nonneg (sub_nonneg.mpr hbc) (show 0 ≤ c ^ 2 - 1 by nlinarith)
  have h₃ := mul_nonneg (sub_nonneg.mpr hca) (show 0 ≤ a ^ 2 - 1 by nlinarith)
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

#print axioms solution
