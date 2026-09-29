-- Prove2me | solution 1 for lean_workbook_plus_53882
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:40.726164+00:00
-- url     : https://prove2.me/submissions/ba0aaeec-924a-4edd-ae61-a565c082ae28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : 30195 - 1346*a + 30195*a^2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a)])
