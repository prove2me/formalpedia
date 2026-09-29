-- Prove2me | solution 1 for lean_workbook_plus_13378
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:47.928866+00:00
-- url     : https://prove2.me/submissions/621d4161-d7cd-414c-839e-266018027b38

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) : (b * c + c * a + a * b + 1) > 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
