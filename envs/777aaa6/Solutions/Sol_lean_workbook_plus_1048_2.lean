-- Prove2me | solution 2 for lean_workbook_plus_1048
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:35:47.80158+00:00
-- url     : https://prove2.me/submissions/0a40ddb9-626f-4b08-bda4-f5db18a0cf70

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (1 / 9) * (2 * a ^ 2 + 2 * c ^ 2 - b ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 - c ^ 2) = a ^ 2 ↔ b ^ 2 + c ^ 2 = 5 * a ^ 2 := by
  constructor <;> intro h <;> linarith
