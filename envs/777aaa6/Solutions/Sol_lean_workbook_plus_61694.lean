-- Prove2me | solution 1 for lean_workbook_plus_61694
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:59.656285+00:00
-- url     : https://prove2.me/submissions/48a725da-fafa-428b-b84a-10b0e6e26153

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^4 + 25 * x^3 + 198 * x^2 + 600 * x + 576 = (x + 4) * (x + 6) * (x^2 + 15 * x + 24) := by
  (intros; linarith)
