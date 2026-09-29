-- Prove2me | solution 1 for lean_workbook_plus_14023
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:12.779779+00:00
-- url     : https://prove2.me/submissions/c926df71-bc9f-45af-ac1f-bf14fa33a462

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : x^2 + 6 * x + 9 = 0) :
  x = -3 := by
  (intros; nlinarith [sq_nonneg (x)])
