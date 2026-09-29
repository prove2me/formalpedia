-- Prove2me | solution 1 for lean_workbook_plus_3670
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:05.811742+00:00
-- url     : https://prove2.me/submissions/95df1ea0-6ea5-4984-bb58-73aef28b170d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) ^ 3 / 4 ≥ a ^ 2 * b + a * b ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
