-- Prove2me | solution 1 for lean_workbook_plus_40785
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:43.098829+00:00
-- url     : https://prove2.me/submissions/1f74f731-c9b4-4a9b-ae59-b462a562d8d9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) : Real.sqrt (a ^ 2 + a * b + b ^ 2) ≥ Real.sqrt 3 / 2 * (a + b) := by
  by_cases h : a + b ≤ 0
  · have : Real.sqrt 3 / 2 * (a + b) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · exact h
    exact le_trans this (Real.sqrt_nonneg _)
  · push_neg at h
    have hpos : 0 ≤ Real.sqrt 3 / 2 * (a + b) := by positivity
    rw [ge_iff_le, Real.le_sqrt hpos]
    · have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg (a - b), h3]
    · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
