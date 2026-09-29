-- Prove2me | solution 1 for lean_workbook_plus_31055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:15.165864+00:00
-- url     : https://prove2.me/submissions/db52595a-b502-4b96-b09e-9f4a3ef86199

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  3 * (a * b * c - 1) ^ 2 + (a - 1) ^ 2 * (b - c) ^ 2 + (b - 1) ^ 2 * (c - a) ^ 2 + (c - 1) ^ 2 * (a - b) ^ 2 + (a + b + c - a * b - b * c - c * a) ^ 2 ≥ 0 := by
  (intros; positivity)
