-- Prove2me | solution 1 for lean_workbook_plus_76974
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:08.049984+00:00
-- url     : https://prove2.me/submissions/91a8d795-03c3-4c97-91e0-041fe56b40fe

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (hab : a ∈ Set.Icc (-1) 1)
    (hbc : b ∈ Set.Icc (-1) 1) (hca : c ∈ Set.Icc (-1) 1) :
    a * (1 - b) + b * (1 - c) + c * (1 - a) + a * b * c ≤ 1 := by
  have h := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hab.2) (sub_nonneg.mpr hbc.2))
    (sub_nonneg.mpr hca.2)
  nlinarith only [h]

#print axioms solution
