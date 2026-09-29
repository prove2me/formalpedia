-- Prove2me | solution 1 for lean_workbook_plus_6295
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:50:03.805852+00:00
-- url     : https://prove2.me/submissions/d9894448-3763-427c-b8c5-2c11fab921a9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b + c) ^ 2 * (a * b + b * c + c * a) - a * b * c * (a + b + c) = (a + b + c) * (a + b) * (b + c) * (c + a) := by
  (intros; linarith)
