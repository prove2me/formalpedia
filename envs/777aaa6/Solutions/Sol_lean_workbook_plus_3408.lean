-- Prove2me | solution 1 for lean_workbook_plus_3408
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:26.567725+00:00
-- url     : https://prove2.me/submissions/190605ca-41c8-41cc-929f-da3d98b426f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b - c) * (a - b + c) = 1 / 4 * (6 * (a * b + a * c + b * c) - 5 * (a ^ 2 + b ^ 2 + c ^ 2) + (b + c - 3 * a) ^ 2) := by
  (intros; linarith)
