-- Prove2me | solution 1 for lean_workbook_plus_52107
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:08.377418+00:00
-- url     : https://prove2.me/submissions/5962e40d-8da9-4562-a693-17294384fc1b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a - (b + c) / 2)^2 + (3 / 4) * (b - c)^2 ≥ 0 := by
  (intros; positivity)
