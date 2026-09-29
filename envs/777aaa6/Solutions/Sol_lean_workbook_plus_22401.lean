-- Prove2me | solution 1 for lean_workbook_plus_22401
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:42.862814+00:00
-- url     : https://prove2.me/submissions/8639605c-fdb0-4973-8b10-0eeea0bc3288

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 1 < x) : 2 / x < 1 + 1 / x ^ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
