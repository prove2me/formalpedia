-- Prove2me | solution 1 for lean_workbook_plus_15029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:55.727301+00:00
-- url     : https://prove2.me/submissions/657dbeb8-1e78-4e1f-8e3a-0f23e880c9b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 → a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  (intros; linarith)
