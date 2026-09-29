-- Prove2me | solution 1 for lean_workbook_plus_71651
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:39.063575+00:00
-- url     : https://prove2.me/submissions/8130798f-066b-45c1-a828-a0c7623bf506

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g o : ℝ) : 0.2 * g + 0.5 * o = 24 → o = 48 - 0.4 * g := by
  (intros; linarith)
