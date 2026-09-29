-- Prove2me | solution 1 for lean_workbook_plus_79794
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:59:55.761702+00:00
-- url     : https://prove2.me/submissions/e8258405-2d7b-4aa1-a471-2ba2910d69e3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ a b c : ℝ, (a^2 + b^2 + c^2)^3 - (a^3 + b^3 + c^3 - a * b * c)^2 = (1 / 2) * (a^2 + b^2) * (a * b + b * c + c * a - c^2)^2 + (1 / 2) * (b^2 + c^2) * (b * c + c * a + a * b - a^2)^2 + (1 / 2) * (c^2 + a^2) * (c * a + a * b + b * c - b^2)^2 + (3 / 2) * a^2 * b^2 * (a^2 + b^2) + (3 / 2) * b^2 * c^2 * (b^2 + c^2) + (3 / 2) * c^2 * a^2 * (c^2 + a^2) + 2 * a^2 * b^2 * c^2 := by
  (intros; linarith)
