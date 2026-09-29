-- Prove2me | solution 1 for lean_workbook_plus_5373
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:31.71539+00:00
-- url     : https://prove2.me/submissions/1dfe13e0-72da-411c-9860-6b86706cd15c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : a ≠ 0) : a ^ 2 > 0 := by
  (intros; positivity)
