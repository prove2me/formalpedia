-- Prove2me | solution 1 for lean_workbook_plus_51111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:15.136669+00:00
-- url     : https://prove2.me/submissions/70b49147-5891-4018-b2a1-499c92d7d794

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + 1 = 3 * a * b) : 1 / a + 1 / b ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
