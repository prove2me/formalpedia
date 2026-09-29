-- Prove2me | solution 1 for lean_workbook_plus_74854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:42.719689+00:00
-- url     : https://prove2.me/submissions/6f64a256-517e-4a59-8d8a-a8186387f2e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x^3 + y^3 + z^3 = (x + y + z) * (x^2 + y^2 + z^2 - x * y - x * z - y * z) + 3 * x * y * z := by
  (intros; linarith)
