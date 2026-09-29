-- Prove2me | solution 1 for lean_workbook_plus_35869
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:00.192055+00:00
-- url     : https://prove2.me/submissions/fb6edd1a-357a-4f5f-b48d-d9acaf289dca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, (x - 1) ^ 2 * ((x ^ 2 + 2) * (x + 1) ^ 2 + 3) ≥ 0 := by
  (intros; positivity)
