-- Prove2me | solution 1 for lean_workbook_plus_33390
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:37.876209+00:00
-- url     : https://prove2.me/submissions/a9da9ef7-cfa8-46fa-a1be-9d35460afdaa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (c^2 - a^2 - b^2)^2 + (a^2 - b^2)^2 ≥ 0 := by
  (intros; positivity)
