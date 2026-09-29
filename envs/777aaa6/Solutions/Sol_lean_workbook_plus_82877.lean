-- Prove2me | solution 1 for lean_workbook_plus_82877
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:53.740621+00:00
-- url     : https://prove2.me/submissions/b1c98a47-9dee-45d3-bc6b-66b0629a9359

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x + x^2 + x^3 = 1) : x^6 + x^4 + 3*x^2 = 1 := by
  (intros; nlinarith [sq_nonneg (x)])
