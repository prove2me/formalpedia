-- Prove2me | solution 1 for lean_workbook_plus_25993
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:04.717045+00:00
-- url     : https://prove2.me/submissions/87dcb1d2-6c1d-4aca-87ef-1d983afe68d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
  (b + d) * (c + a) * (a * c * d + a * b * d + b * c * a + b * d * c) - 4 * (a + b + c + d) * (a * b * c * d) =
    (b - d) ^ 2 * a ^ 2 * c + (a - c) ^ 2 * b * d ^ 2 + (d - b) ^ 2 * c ^ 2 * a + (c - a) ^ 2 * b ^ 2 * d := by
  (intros; linarith)
