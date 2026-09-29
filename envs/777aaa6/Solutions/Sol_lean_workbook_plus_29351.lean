-- Prove2me | solution 1 for lean_workbook_plus_29351
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:03:50.734118+00:00
-- url     : https://prove2.me/submissions/24da8006-2592-4d4b-b51f-45aa3a3fb2c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a * b ≤ 1 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
