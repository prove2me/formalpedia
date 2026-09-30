-- Prove2me | solution 2 for lean_workbook_plus_26681
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:53.980737+00:00
-- url     : https://prove2.me/submissions/6df293b5-b24b-4f12-9faf-3087cf1444fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 4 * b ^ 2 * c ^ 2 - (b ^ 2 + c ^ 2 - a ^ 2) ^ 2 = (a - b + c) * (a + b - c) * (b + c - a) * (b + c + a) := by
  (intros; linarith)
