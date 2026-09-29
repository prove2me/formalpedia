-- Prove2me | solution 1 for lean_workbook_plus_29213
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:38.102291+00:00
-- url     : https://prove2.me/submissions/056d9ce3-ad26-47e6-8c25-ce61fb8436d6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a^3 = 2*a - 3) (h' : a^4 = 2*a^2 - 3*a) : a^3 - a^4 = -2*a^2 + 5*a - 3 := by
  (intros; linarith)
