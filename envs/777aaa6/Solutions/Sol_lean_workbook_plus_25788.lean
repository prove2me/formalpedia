-- Prove2me | solution 1 for lean_workbook_plus_25788
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:27.030705+00:00
-- url     : https://prove2.me/submissions/6c0ddd22-ca9b-4259-9655-302940afd2d2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 / (2 * a ^ 2 * b ^ 2 * c ^ 2) ≥ 0 := by
  (intros; positivity)
