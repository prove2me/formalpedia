-- Prove2me | solution 1 for lean_workbook_plus_29291
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:33.206322+00:00
-- url     : https://prove2.me/submissions/c57eadf0-7fd4-41e9-83a5-8c4ed66d08e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x^2 = x) : x^3 = x^2 := by
  (intros; nlinarith [sq_nonneg (x)])
