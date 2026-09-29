-- Prove2me | solution 1 for lean_workbook_plus_3332
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:39.408014+00:00
-- url     : https://prove2.me/submissions/0ce800b1-c218-498b-9a1b-6c69793b7dee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, (x - 1) ^ 2 * ((x ^ 2 - 1) ^ 2 + x ^ 2) ≥ 0 := by
  (intros; positivity)
