-- Prove2me | solution 1 for lean_workbook_plus_17220
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:42.458638+00:00
-- url     : https://prove2.me/submissions/7bdb5667-aa04-40e0-9785-bb2bed1be09d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) :
  a * (c - d) * (a * c - b ^ 2 - a * d + c * d) + b * (d - a) * (a * d - c ^ 2 - a * b + b * d) + c * (a - b) * (a * b - d ^ 2 - b * c + c * a) + d * (b - c) * (b * c - a ^ 2 - c * d + d * b) =
  1 / 4 * (a * b - a * d - b * c + c * a - b * d + d * c) ^ 2 + 1 / 8 * (b - d) ^ 2 * (a - c) ^ 2 + 3 / 4 * (b * d - a * c) ^ 2 + 3 / 4 * (a * c - b * d) ^ 2 + 1 / 4 * (a * d - a * b - a * c + b * c - c * d + b * d) ^ 2 + 1 / 8 * (-a + c) ^ 2 * (b - d) ^ 2 + 1 / 8 * (-b + d) ^ 2 * (-a + c) ^ 2 + 1 / 8 * (a - c) ^ 2 * (-b + d) ^ 2 := by
  (intros; linarith)
