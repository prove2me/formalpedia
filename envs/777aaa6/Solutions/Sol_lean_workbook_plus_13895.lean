-- Prove2me | solution 1 for lean_workbook_plus_13895
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:00.24064+00:00
-- url     : https://prove2.me/submissions/551343fb-5d25-40dd-b854-f4b84f34554e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a + b - c) ^ 3 + (a - b + c) ^ 3 + (b + c - a) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + 3 * (a ^ 2 * b + a * b ^ 2 + a * c ^ 2 + a ^ 2 * c + b ^ 2 * c + b * c ^ 2 - 6 * a * b * c) := by
  (intros; linarith)
