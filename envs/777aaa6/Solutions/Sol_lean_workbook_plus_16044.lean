-- Prove2me | solution 1 for lean_workbook_plus_16044
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:36.680298+00:00
-- url     : https://prove2.me/submissions/4d3716c2-539d-440d-a645-aea67d10fd95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a^3 - 3*a = -11) : a^6 - 6*a^4 + 8*a^3 + 9*a^2 - 24*a + 16 = 49 := by
  (intros; nlinarith [sq_nonneg (a)])
