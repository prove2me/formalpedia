-- Prove2me | solution 1 for lean_workbook_plus_16379
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:08.118836+00:00
-- url     : https://prove2.me/submissions/4a46c042-9f03-4851-b1c0-5995c2246251

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (b - c) ^ 2 * (a - c) ^ 2 + (c - a) ^ 2 * (b - a) ^ 2 + (a - b) ^ 2 * (c - b) ^ 2 = (b ^ 2 - 2 * b * c + c ^ 2) * (a ^ 2 - 2 * a * c + c ^ 2) + (c ^ 2 - 2 * c * a + a ^ 2) * (b ^ 2 - 2 * b * a + a ^ 2) + (a ^ 2 - 2 * a * b + b ^ 2) * (c ^ 2 - 2 * c * b + b ^ 2) := by
  (intros; linarith)
