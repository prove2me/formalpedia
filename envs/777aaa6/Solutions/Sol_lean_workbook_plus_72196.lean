-- Prove2me | solution 1 for lean_workbook_plus_72196
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:26.288285+00:00
-- url     : https://prove2.me/submissions/ea6449de-1939-44aa-b623-8a9bf4e72444

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (1 / 2) * ((a - b) ^ 2 * (a ^ 2 + b ^ 2) + (b - c) ^ 2 * (b ^ 2 + c ^ 2) + (c - a) ^ 2 * (c ^ 2 + a ^ 2)) ≥ 0 := by
  (intros; positivity)
