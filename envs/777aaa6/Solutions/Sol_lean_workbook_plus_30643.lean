-- Prove2me | solution 1 for lean_workbook_plus_30643
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:51.956853+00:00
-- url     : https://prove2.me/submissions/9210f088-d177-427b-8a78-70c7058a225e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (1 / 8) * (a - b) ^ 2 * (2 * a + 2 * b + 17 * c) ^ 2 + (1 / 8) * (b - c) ^ 2 * (2 * b + 2 * c + 17 * a) ^ 2 + (1 / 8) * (c - a) ^ 2 * (2 * c + 2 * a + 17 * b) ^ 2 ≥ 0 := by
  (intros; positivity)
