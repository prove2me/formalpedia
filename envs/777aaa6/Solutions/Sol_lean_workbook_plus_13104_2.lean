-- Prove2me | solution 2 for lean_workbook_plus_13104
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:13.223272+00:00
-- url     : https://prove2.me/submissions/19f18acd-917f-4a21-840d-87a27705c344

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ a b c : ℝ, 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + 9 ≥ 6 * (a + b + c) := by
  intro a b c
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
