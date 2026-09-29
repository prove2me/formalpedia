-- Prove2me | solution 1 for lean_workbook_plus_56820
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:55.505349+00:00
-- url     : https://prove2.me/submissions/2c5f7296-ac3f-4e22-935b-c73c1d8377cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = 3) : (x^2 - 6*x + 5) / (x^2 + 2*x + 2) = -4/17 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
