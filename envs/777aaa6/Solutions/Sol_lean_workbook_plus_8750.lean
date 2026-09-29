-- Prove2me | solution 1 for lean_workbook_plus_8750
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:59.699018+00:00
-- url     : https://prove2.me/submissions/08ec34db-2de2-4ebd-8690-f8452417dc4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b = 1 → a * b ≤ 1 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
