-- Prove2me | solution 1 for lean_workbook_plus_5971
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:18.072513+00:00
-- url     : https://prove2.me/submissions/364929b9-33ed-4c1b-b16d-95bdc1d04f00

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
  -(b + d) * (c + a) * (a * c * d + a * b * d + a * b * c + b * c * d) + (a + b + c + d) * (a * b + c * d) * (b * c + a * d) =
  (a - c) ^ 2 * b * c * d + (b - d) ^ 2 * a * c * d + (c - a) ^ 2 * a * b * d + (d - b) ^ 2 * a * b * c := by
  (intros; linarith)
