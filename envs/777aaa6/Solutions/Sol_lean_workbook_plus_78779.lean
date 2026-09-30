-- Prove2me | solution 1 for lean_workbook_plus_78779
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:33:50.211971+00:00
-- url     : https://prove2.me/submissions/b2383703-efd2-4fcb-9a53-6a36a07578fc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    a * b + b * c + c * a ≤ 2 * a * b * c + 1 := by
  have hab : a * b ≤ 1 := by
    calc
      a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha.2 hb.1
      _ ≤ 1 := by simpa using hb.2
  have h₁ := mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hab)
  have h₂ := mul_nonneg hc.1
    (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))
  nlinarith

#print axioms solution
