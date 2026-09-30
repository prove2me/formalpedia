-- Prove2me | solution 2 for lean_workbook_plus_59379
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:41.215516+00:00
-- url     : https://prove2.me/submissions/b9fa6162-dc16-4ae0-a1a5-dd0cb5bdcd12

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c <= 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
