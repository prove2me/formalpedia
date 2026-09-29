-- Prove2me | solution 1 for lean_workbook_plus_55358
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:46.005434+00:00
-- url     : https://prove2.me/submissions/5d6efe97-88d8-491c-a172-3af96cce8ebc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0 := by
  (intros; positivity)
