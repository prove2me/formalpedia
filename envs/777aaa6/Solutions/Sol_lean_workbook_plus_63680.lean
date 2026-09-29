-- Prove2me | solution 1 for lean_workbook_plus_63680
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:52.333962+00:00
-- url     : https://prove2.me/submissions/960b92b4-19aa-4893-b6de-bc2fb29e5f2b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 >= 0 := by
  (intros; positivity)
