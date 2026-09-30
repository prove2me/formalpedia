-- Prove2me | solution 1 for lean_workbook_plus_44976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:45:03.291672+00:00
-- url     : https://prove2.me/submissions/4d459814-4c85-4666-82df-bc360c67c987

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b) (hc : 0 < c) :
    a * Real.sqrt (b * c) ≤ Real.sqrt (a * b * c) := by
  have hbc : 0 ≤ b * c := le_of_lt (mul_pos hb hc)
  have haa : a ^ 2 ≤ a := by nlinarith [ha.1, ha.2]
  have hmul := mul_le_mul_of_nonneg_right haa hbc
  apply Real.le_sqrt_of_sq_le
  calc
    (a * Real.sqrt (b * c)) ^ 2 = a ^ 2 * (b * c) := by
      rw [mul_pow, Real.sq_sqrt hbc]
    _ ≤ a * (b * c) := hmul
    _ = a * b * c := by ring

#print axioms solution
