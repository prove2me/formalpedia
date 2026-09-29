-- Prove2me | solution 1 for lean_workbook_plus_2143
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:30.487341+00:00
-- url     : https://prove2.me/submissions/375b819d-329b-4a49-92f2-f91f1cb2c0cd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, 4 * (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) - ((a + b) * (b + c) * (c + a) - 6 * a * b * c)^2 = 3 * (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  (intros; linarith)
