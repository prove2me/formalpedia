-- Prove2me | solution 2 for lean_workbook_plus_17090
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:02.066777+00:00
-- url     : https://prove2.me/submissions/c09d3734-f0ca-47b1-a67f-fcfc0da9947e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
