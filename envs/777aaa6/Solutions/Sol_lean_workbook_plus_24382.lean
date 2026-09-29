-- Prove2me | solution 1 for lean_workbook_plus_24382
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:23.625065+00:00
-- url     : https://prove2.me/submissions/22e25bbf-fd4d-4904-a4ff-903020700de2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + 5*b + 9*c = 1) (h2 : 4*a + 2*b + 3*c = 2) (h3 : 7*a + 8*b + 6*c = 9) : 741*a + 825*b + 639*c = 921 := by
  (intros; linarith)
