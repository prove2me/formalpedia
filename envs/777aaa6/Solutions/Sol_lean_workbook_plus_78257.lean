-- Prove2me | solution 1 for lean_workbook_plus_78257
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:58.430289+00:00
-- url     : https://prove2.me/submissions/2dd47993-5a88-45f3-9404-544cb3a76a8c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
    (ha : 0 < a ∧ 0 < b ∧ 0 < c)
    (hab : a + b > c)
    (hbc : b + c > a)
    (hca : a + c > b) :
    a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
