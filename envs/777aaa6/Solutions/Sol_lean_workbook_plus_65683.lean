-- Prove2me | solution 1 for lean_workbook_plus_65683
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:17.613932+00:00
-- url     : https://prove2.me/submissions/49e57ebe-c4b0-4998-8db4-e1f8ba4cb72c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b - c) * (a + c - b) * (b + c - a) + 2 * a * b * c = a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c) := by
  (intros; linarith)
