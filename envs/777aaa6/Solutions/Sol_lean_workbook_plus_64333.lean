-- Prove2me | solution 1 for lean_workbook_plus_64333
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:51.328218+00:00
-- url     : https://prove2.me/submissions/2f20c4aa-a75b-4f03-b1f6-b123a0f9a58b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * d - b * c) ^ 2 ≥ 0 := by
  (intros; positivity)
