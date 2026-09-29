-- Prove2me | solution 1 for lean_workbook_plus_6727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:12.167116+00:00
-- url     : https://prove2.me/submissions/d7c5e8d6-4595-466f-911b-2412a3ba7707

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℂ) (a b c d : ℂ) :
  (a - x) * (d - x) - b * c = x^2 - (a + d) * x + (a * d - b * c) := by
  (intros; ring)
