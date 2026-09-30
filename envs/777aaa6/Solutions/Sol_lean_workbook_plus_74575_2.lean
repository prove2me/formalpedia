-- Prove2me | solution 2 for lean_workbook_plus_74575
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:20.397188+00:00
-- url     : https://prove2.me/submissions/ae484cda-2b6f-4890-ba49-09003193e430

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + (b + c) / 4) * (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)) = b * c * (b - c) ^ 2 + (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 + (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
  (intros; linarith)
