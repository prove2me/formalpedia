-- Prove2me | solution 1 for lean_workbook_plus_79649
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:17.754726+00:00
-- url     : https://prove2.me/submissions/620f6c34-2c73-401a-a49c-e7a876041938

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 < x) : 4 * (x ^ 7 + 1) > x + 1 := by
  by_cases h : x ≤ 1
  · nlinarith [pow_pos hx 7]
  · push_neg at h
    nlinarith [pow_pos hx 7, sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - 1),
      mul_pos hx hx, mul_pos (mul_pos hx hx) hx]
