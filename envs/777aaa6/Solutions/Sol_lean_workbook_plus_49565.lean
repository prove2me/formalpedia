-- Prove2me | solution 1 for lean_workbook_plus_49565
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:02.253466+00:00
-- url     : https://prove2.me/submissions/a5e971d4-1c22-43a6-a416-00293234b984

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ a b c : ℝ,
    (a - 1) ^ 2 * (b - 2) ^ 2 / (6 * (a ^ 2 + 2)) +
    (b - 1) ^ 2 * (c - 2) ^ 2 / (6 * (b ^ 2 + 2)) +
    (c - 1) ^ 2 * (a - 2) ^ 2 / (6 * (c ^ 2 + 2)) ≥
    0 := by
  (intros; positivity)
