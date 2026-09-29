-- Prove2me | solution 1 for lean_workbook_plus_46118
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:17.930612+00:00
-- url     : https://prove2.me/submissions/d4faeeeb-767a-42c4-a881-d722fee8efa8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : b^2 < 4 * a * c) : 3 * b < 2 * a + 6 * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
