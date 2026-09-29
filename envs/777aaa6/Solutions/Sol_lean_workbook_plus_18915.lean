-- Prove2me | solution 1 for lean_workbook_plus_18915
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:22.910115+00:00
-- url     : https://prove2.me/submissions/1fc0b28e-3605-4db7-bfdd-ce2c1bd9cafa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h₀ : 1 < a) : 2 * a + 1 < 3 * a := by
  (intros; linarith)
