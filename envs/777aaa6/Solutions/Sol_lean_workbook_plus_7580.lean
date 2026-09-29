-- Prove2me | solution 1 for lean_workbook_plus_7580
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:52.96359+00:00
-- url     : https://prove2.me/submissions/51b9581d-664f-48a2-a671-7f9737237a6c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
  (a + b) * (b + c) * (c + d) * (d + a) * (c + a) * (b + d) - (2 / 3) * (a + b + c + d) * (a * b + b * c + c * d + d * a + a * c + b * d) * (a * c * d + a * b * d + a * b * c + b * c * d) =
  (1 / 6) * (a * b - c * d) ^ 2 * b * d + (1 / 6) * (b * c - a * d) ^ 2 * a * c + (1 / 6) * (a * d - b * c) ^ 2 * a * c + (1 / 3) * (b * d - a * c) ^ 2 * b * c + (1 / 3) * (a * c - b * d) ^ 2 * a * b + (1 / 3) * (b * d - a * c) ^ 2 * a * d + (1 / 3) * (a * c - b * d) ^ 2 * c * d + (1 / 6) * (c * d - a * b) ^ 2 * b * d + (a * d - b * c) ^ 2 * (b * d / 6 + c * d / 3) + (a * b - c * d) ^ 2 * (a * c / 6 + a * d / 3) + (b * c - a * d) ^ 2 * (b * d / 6 + a * b / 3) + (c * d - a * b) ^ 2 * (a * c / 6 + b * c / 3) := by
  (intros; linarith)
