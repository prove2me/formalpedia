-- Prove2me | solution 1 for lean_workbook_plus_51309
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:18:56.089259+00:00
-- url     : https://prove2.me/submissions/b25f67a0-592f-4c16-b53d-1880740fcadc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 2 * a * b * c * (a + b + c) = 1 / 2 * ((a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2) + (a * b + b * c + c * a)^2 := by
  (intros; linarith)
