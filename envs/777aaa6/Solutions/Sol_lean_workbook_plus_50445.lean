-- Prove2me | solution 1 for lean_workbook_plus_50445
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:29.201741+00:00
-- url     : https://prove2.me/submissions/f676c69e-9529-44e0-9446-9c0862ea03d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*((a - b)^2 + (b - c)^2 + (c - a)^2)/2 := by
  (intros; linarith)
