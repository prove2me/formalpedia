-- Prove2me | solution 1 for lean_workbook_plus_81283
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:19.655739+00:00
-- url     : https://prove2.me/submissions/c6bc6984-a47e-4876-8c0d-4d6e6d60f779

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a v : ℂ, (a - 3 * v) * (a - v) * (a + v) * (a + 3 * v) + (2 * v) ^ 4 = (a ^ 2 - v ^ 2) * (a ^ 2 - 9 * v ^ 2) + 16 * v ^ 4 := by
  (intros; ring)
