-- Prove2me | solution 1 for lean_workbook_plus_70205
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:40.765766+00:00
-- url     : https://prove2.me/submissions/eb938ab3-2c05-417a-b0f5-afbc3a890b33

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) = 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4) := by
  (intros; linarith)
