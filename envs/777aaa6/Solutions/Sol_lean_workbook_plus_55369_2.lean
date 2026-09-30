-- Prove2me | solution 2 for lean_workbook_plus_55369
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:48.700762+00:00
-- url     : https://prove2.me/submissions/32892467-357c-4ce2-8264-27667c9f78a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) : x 1 + 4 * x 2 + 9 * x 3 + 16 * x 4 + 25 * x 5 + 36 * x 6 + 49 * x 7 = 1 ∧ 4 * x 1 + 9 * x 2 + 16 * x 3 + 25 * x 4 + 36 * x 5 + 49 * x 6 + 64 * x 7 = 12 ∧ 9 * x 1 + 16 * x 2 + 25 * x 3 + 36 * x 4 + 49 * x 5 + 64 * x 6 + 81 * x 7 = 123 → 16 * x 1 + 25 * x 2 + 36 * x 3 + 49 * x 4 + 64 * x 5 + 81 * x 6 + 100 * x 7 = 334 := by
  (intros; linarith)
