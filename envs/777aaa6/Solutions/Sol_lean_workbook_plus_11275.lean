-- Prove2me | solution 1 for lean_workbook_plus_11275
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:57.944447+00:00
-- url     : https://prove2.me/submissions/56f8efc6-395e-4cbb-a555-4ac717258298

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a - b) ^ 2 + (a * b - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
