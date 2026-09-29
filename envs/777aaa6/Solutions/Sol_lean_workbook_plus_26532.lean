-- Prove2me | solution 1 for lean_workbook_plus_26532
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:39.723049+00:00
-- url     : https://prove2.me/submissions/14a23c8d-c3a3-47a1-a01f-f57ff46ce1c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, -3 * (a + b + c + d) * (a * c * d + a * b * d + a * b * c + b * c * d) + (a + b) ^ 2 * (c + d) ^ 2 + (b + c) ^ 2 * (d + a) ^ 2 + (c + a) ^ 2 * (b + d) ^ 2 = 3 / 4 * d ^ 2 * (a - b) ^ 2 + 3 / 4 * b ^ 2 * (c - d) ^ 2 + 3 / 4 * a ^ 2 * (b - c) ^ 2 + 1 / 4 * a ^ 2 * (b - 2 * d + c) ^ 2 + 1 / 4 * c ^ 2 * (a - 2 * b + d) ^ 2 + 1 / 4 * d ^ 2 * (a - 2 * c + b) ^ 2 + 3 / 4 * (d - a) ^ 2 * c ^ 2 + 1 / 4 * (c - 2 * a + d) ^ 2 * b ^ 2 := by
  (intros; linarith)
