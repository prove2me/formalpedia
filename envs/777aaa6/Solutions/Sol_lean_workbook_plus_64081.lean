-- Prove2me | solution 1 for lean_workbook_plus_64081
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:17.36431+00:00
-- url     : https://prove2.me/submissions/8aba629d-2cc8-4581-9ac1-245d86a00dd1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, -a^3 + a^2 * b + a * b^2 - b^3 + a^2 * c - 2 * a * b * c + b^2 * c + a * c^2 + b * c^2 - c^3 = (a + b - c) * (a + c - b) * (b + c - a) := by
  (intros; linarith)
