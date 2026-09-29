-- Prove2me | solution 1 for lean_workbook_plus_79940
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:29.000354+00:00
-- url     : https://prove2.me/submissions/1973c7b9-cb0e-4c8a-bbbf-a6ff6e666101

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℂ, x^8 - 14 * x^4 - 8 * x^3 - x^2 + 1 = 0 ↔ (x^4 + 1)^2 - x^2 * (4 * x + 1)^2 = 0 := by
  (intros; ring)
