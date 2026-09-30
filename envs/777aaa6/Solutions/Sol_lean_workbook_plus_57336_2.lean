-- Prove2me | solution 2 for lean_workbook_plus_57336
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:22.129063+00:00
-- url     : https://prove2.me/submissions/7becb908-6372-4fd3-ad4d-a39c9c875a52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  14 * (a ^ 2 + b ^ 2) + 53 * a * b ≤ (81 / 4) * (a + b) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
