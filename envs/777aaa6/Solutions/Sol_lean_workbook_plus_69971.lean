-- Prove2me | solution 1 for lean_workbook_plus_69971
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:04.532444+00:00
-- url     : https://prove2.me/submissions/38fda458-d08f-4dc9-9705-5232742f0697

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : k * (a + b) = 1 + a * b) (hk : 1 ≤ k) : a + b + 1 / a + 1 / b ≥ 4 * k := by
  (intros; field_simp; nlinarith [sq_nonneg (k), sq_nonneg (a), sq_nonneg (b), sq_nonneg (k - a), sq_nonneg (k - b), sq_nonneg (a - b), sq_nonneg (k + a), sq_nonneg (k + b), sq_nonneg (a + b), mul_pos ha hb])
