-- Prove2me | solution 1 for lean_workbook_plus_2833
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:57.678581+00:00
-- url     : https://prove2.me/submissions/de3ca947-c2ca-4789-b11e-ddf2b4a8e384

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 1) :
  ∑ i, (∏ j, if j ≠ i then Real.sqrt (a j ^ n) * Real.sqrt (1 - a i) else 0) ≤ 1 := by
  have h : ∀ i : Fin n, (∏ j, if j ≠ i then Real.sqrt (a j ^ n) * Real.sqrt (1 - a i) else 0) = 0 := by
    intro i
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simp only [h, Finset.sum_const_zero]
  norm_num
