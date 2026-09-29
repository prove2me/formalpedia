-- Prove2me | solution 1 for lean_workbook_plus_56647
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:37.331321+00:00
-- url     : https://prove2.me/submissions/7b11287b-1d2a-4c5b-9ba6-07cecee12650

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 5 * a ^ 2 + 8 * b ^ 2 + 9 * c ^ 2 ≥ 4 * a * b + 12 * b * c + 6 * c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
