-- Prove2me | solution 1 for lean_workbook_plus_55173
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:33.958705+00:00
-- url     : https://prove2.me/submissions/1b82179a-3547-4443-9f26-4ec52654d01c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 * b^2 + b^2 * c^2 ≥ 2 * a * b^2 * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
