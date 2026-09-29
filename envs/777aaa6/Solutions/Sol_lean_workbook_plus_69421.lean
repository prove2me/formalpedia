-- Prove2me | solution 1 for lean_workbook_plus_69421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:49.502414+00:00
-- url     : https://prove2.me/submissions/43cf4491-b2ff-43c2-b71b-8723a6e919cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : ((√a - √b) ^ 2 + (√a - √c) ^ 2 + (√c - √b) ^ 2) / 2 ≥ 0 := by
  (intros; positivity)
