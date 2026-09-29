-- Prove2me | solution 1 for lean_workbook_plus_2428
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:48.215172+00:00
-- url     : https://prove2.me/submissions/074674bf-6918-4d81-9832-8a29b412e1ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 2 * b) (h : 2 * b ≤ 3 * a) : a^2 + b^2 ≤ 5 / 2 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
