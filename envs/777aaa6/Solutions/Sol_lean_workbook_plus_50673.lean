-- Prove2me | solution 1 for lean_workbook_plus_50673
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:58.307132+00:00
-- url     : https://prove2.me/submissions/8bbecdb1-0933-4c42-9918-14d43d9f6ba3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, a * c ^ 4 + b * d ^ 4 + a ^ 4 * c + b ^ 4 * d - a ^ 2 * c ^ 3 - b ^ 2 * d ^ 3 - a ^ 3 * c ^ 2 - b ^ 3 * d ^ 2 = (a - c) ^ 2 * a ^ 2 * c + (b - d) ^ 2 * b ^ 2 * d + (c - a) ^ 2 * c ^ 2 * a + (d - b) ^ 2 * b * d ^ 2 := by
  (intros; linarith)
