-- Prove2me | solution 2 for lean_workbook_plus_48710
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:27.857963+00:00
-- url     : https://prove2.me/submissions/82ca62fa-3abc-4e18-ab87-6121d315cea3

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 3 * b + a * b ^ 3 + b ^ 3 * c + b * c ^ 3 + c ^ 3 * a + c * a ^ 3 := by
  intro a b c
  nlinarith [sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b), sq_nonneg (b ^ 2 - b * c),
    sq_nonneg (c ^ 2 - b * c), sq_nonneg (c ^ 2 - c * a), sq_nonneg (a ^ 2 - c * a)]
