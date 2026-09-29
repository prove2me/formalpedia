-- Prove2me | solution 1 for lean_workbook_plus_21642
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:13.058208+00:00
-- url     : https://prove2.me/submissions/72b69e30-5cab-4cd6-94df-8d564682e1a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℤ, (a - b) ^ 3 + (b - c) ^ 3 + (c - a) ^ 3 - (a + b - c) * (b - a) * (a - c) - (b + c - a) * (c - b) * (b - a) - (c + a - b) * (a - c) * (c - b) = a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
  (intros; linarith)
