-- Prove2me | solution 1 for lean_workbook_plus_34205
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:21.82519+00:00
-- url     : https://prove2.me/submissions/bd1d606c-f713-4e2f-9ad4-e5a8940392e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  3 * a ^ 2 + (b + c) ^ 2 - 4 * a * c =
    (a - b - c) ^ 2 + (a - b + c) * (a + b - c) + (a + b - c) ^ 2 := by
  (intros; linarith)
