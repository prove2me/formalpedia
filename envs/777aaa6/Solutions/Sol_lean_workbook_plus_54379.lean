-- Prove2me | solution 1 for lean_workbook_plus_54379
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:48.732775+00:00
-- url     : https://prove2.me/submissions/0d8120fa-60e6-48b8-83b5-91cc9b9e0edd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 3 + b ^ 3 = 2) : a + b ≤ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
