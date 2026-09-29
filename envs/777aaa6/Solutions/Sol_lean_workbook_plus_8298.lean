-- Prove2me | solution 1 for lean_workbook_plus_8298
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:15.937165+00:00
-- url     : https://prove2.me/submissions/96dfa665-8eea-4248-ab25-e7f96cd549d9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, (x - 1) ^ 2 * (x ^ 2 + 1) * (3 * (x + 5 / 6) ^ 2 + 11 / 12) ≥ 0 := by
  (intros; positivity)
