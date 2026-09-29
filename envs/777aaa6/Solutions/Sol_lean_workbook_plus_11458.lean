-- Prove2me | solution 1 for lean_workbook_plus_11458
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:18.594015+00:00
-- url     : https://prove2.me/submissions/cb246ab7-3b79-4232-a928-9036238aa6a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e f : ℝ) : (-(a * d + b * e + c * f) ^ 2 + 3 / 2 * a ^ 3 * d + 3 / 2 * b ^ 3 * e + 3 / 2 * c ^ 3 * f + 3 / 2 * d ^ 3 * a + 3 / 2 * e ^ 3 * b + 3 / 2 * f ^ 3 * c) = 3 / 4 * (f - c) ^ 2 * f * c + 3 / 4 * (d - a) ^ 2 * d * a + 3 / 4 * (e - b) ^ 2 * e * b + 3 / 4 * (b - e) ^ 2 * b * e + 3 / 4 * (c - f) ^ 2 * c * f + 3 / 4 * (a - d) ^ 2 * a * d + 1 / 3 * (2 * a * d - b * e - c * f) ^ 2 + 1 / 3 * (2 * b * e - a * d - c * f) ^ 2 + 1 / 3 * (2 * c * f - a * d - b * e) ^ 2 := by
  (intros; linarith)
