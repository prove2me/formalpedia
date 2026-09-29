-- Prove2me | solution 1 for lean_workbook_plus_60638
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:23.590906+00:00
-- url     : https://prove2.me/submissions/f4d45fc2-f959-4ab7-87ea-2fe99cb9f970

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x = 2004.5) :
  6 * ((x - 3 / 2)^2 + (x - 1 / 2)^2 + (x + 1 / 2)^2 + (x + 3 / 2)^2 + 4 * x) = 6 * (4 * x^2 + 4 * x + 5) := by
  (intros; linarith)
