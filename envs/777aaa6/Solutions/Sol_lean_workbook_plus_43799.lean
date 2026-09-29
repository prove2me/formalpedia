-- Prove2me | solution 1 for lean_workbook_plus_43799
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:55.65636+00:00
-- url     : https://prove2.me/submissions/24b404a9-6855-456d-90df-b31d18a2b7f9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, (a - 1 / 2)^2 + (b - 1 / 2)^2 + (c - 1 / 2)^2 + (d - 1 / 2)^2 >= 0 := by
  (intros; positivity)
