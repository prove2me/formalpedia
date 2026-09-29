-- Prove2me | solution 1 for lean_workbook_plus_34315
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:41.320594+00:00
-- url     : https://prove2.me/submissions/e11b1731-9e5b-43e2-85a4-839261b2a58c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 4 * (a + b + c) ^ 3 ≥ 9 * (a * b + b * c + c * a) + 27 * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
