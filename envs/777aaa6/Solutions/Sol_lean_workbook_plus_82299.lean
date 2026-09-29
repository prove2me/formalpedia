-- Prove2me | solution 1 for lean_workbook_plus_82299
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T02:17:16.949976+00:00
-- url     : https://prove2.me/submissions/ceb32508-0bdf-48b6-9c32-0561a688a4de

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, (a + b + c) ^ 2 - 4 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 0 := by
  intro a b c
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    sq_nonneg a, sq_nonneg b, sq_nonneg c]
