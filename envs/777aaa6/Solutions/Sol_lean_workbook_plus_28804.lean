-- Prove2me | solution 1 for lean_workbook_plus_28804
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:56:07.618937+00:00
-- url     : https://prove2.me/submissions/a59dfa7e-888f-4409-952e-08c76e18d0e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ) : (77 * t - 147) / 6 ≥ 0 → t ≥ 21 / 11 := by
  (intros; linarith)
