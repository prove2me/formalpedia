-- Prove2me | solution 1 for lean_workbook_plus_47195
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:28.323816+00:00
-- url     : https://prove2.me/submissions/1a54a143-0b45-4ab3-8483-4689f36cf6b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : 2 * (b ^ 2 + c ^ 2) + 5 * b * c ≤ (9 / 4) * (b + c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
