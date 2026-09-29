-- Prove2me | solution 1 for lean_workbook_plus_1405
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:57.468511+00:00
-- url     : https://prove2.me/submissions/07088e11-49c8-4cb1-a118-c73ea67b051c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
