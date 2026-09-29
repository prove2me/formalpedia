-- Prove2me | solution 1 for lean_workbook_plus_5809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:03.665436+00:00
-- url     : https://prove2.me/submissions/cdac1821-a455-4aa4-afaf-b8e8d905a90c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
  (b + d) * (c + a) * (a * b^2 + b * c^2 + c * d^2 + a^2 * d) - 4 * (a + b + c + d) * a * b * c * d =
    (a * b - c * d)^2 * b + (a * d - b * c)^2 * a + (c * d - a * b)^2 * d + (b * c - a * d)^2 * c +
    (a - c)^2 * b * c * d + (b - d)^2 * a * c * d + (c - a)^2 * a * b * d + (d - b)^2 * a * b * c := by
  (intros; linarith)
