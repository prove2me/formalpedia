-- Prove2me | solution 1 for lean_workbook_plus_55596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:12.803122+00:00
-- url     : https://prove2.me/submissions/a44679e6-c415-45dd-803f-21c1ca5ab957

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) - 2 * (b^3 * c + c^3 * b + c^3 * a + a^3 * c + a^3 * b + b^3 * a) = (a^2 + b^2 + c^2 - b * c - c * a - a * b)^2 := by
  (intros; linarith)
