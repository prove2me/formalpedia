-- Prove2me | solution 1 for lean_workbook_plus_57046
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:08.092947+00:00
-- url     : https://prove2.me/submissions/b3c5bcad-9e8a-42a4-afd4-73d5b27020d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c : ℝ) : -7 * (c - 1 / 2) ^ 2 - 1 / 4 ≤ 0 := by
  (intros; nlinarith [sq_nonneg (c)])
