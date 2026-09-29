-- Prove2me | solution 1 for lean_workbook_plus_65111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:27.643762+00:00
-- url     : https://prove2.me/submissions/f22c9724-4258-4ed1-a9b7-f82b1761cfd0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x u : ℝ) : f (x + u) - (x + u) ^ 4 = f x - x ^ 4 → f (x + u) - f x = 4 * x ^ 3 * u + 6 * x ^ 2 * u ^ 2 + 4 * x * u ^ 3 + u ^ 4 := by
  (intros; linarith)
