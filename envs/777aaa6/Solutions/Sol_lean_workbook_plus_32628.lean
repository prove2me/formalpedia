-- Prove2me | solution 1 for lean_workbook_plus_32628
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:30.23336+00:00
-- url     : https://prove2.me/submissions/3016de68-5b77-47bb-9c33-b3021041b0fa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 - a*c)^2 + (b^2 - a*b)^2 + (c^2 - b*c)^2 ≥ 0 := by
  (intros; positivity)
