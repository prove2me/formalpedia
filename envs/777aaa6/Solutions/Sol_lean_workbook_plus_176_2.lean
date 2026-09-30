-- Prove2me | solution 2 for lean_workbook_plus_176
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:11.585125+00:00
-- url     : https://prove2.me/submissions/116dafce-82c1-4616-8758-dec2f6ab6b46

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) (hs : 9 / 4 ≤ s ∧ s ≤ 3) : 4 * s ^ 2 - 21 * s + 27 ≤ 0 := by
  (intros; nlinarith [sq_nonneg (s)])
