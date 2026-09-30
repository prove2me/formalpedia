-- Prove2me | solution 1 for lean_workbook_plus_2836
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:52.627653+00:00
-- url     : https://prove2.me/submissions/ce68876f-d917-4ef4-9902-030cd44bf6c1

import Mathlib

theorem solution (n : ℕ) (x : Fin n → ℝ) (h : ∑ i, x i ^ 2 = 0) : ∀ i, x i = 0 := by
  intro i
  have hi : x i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi
