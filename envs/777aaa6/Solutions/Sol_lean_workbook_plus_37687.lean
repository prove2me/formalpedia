-- Prove2me | solution 1 for lean_workbook_plus_37687
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:09.62805+00:00
-- url     : https://prove2.me/submissions/1efdfc66-2af7-4982-8dc3-eb7af1b6237a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h m f : ℝ) : 3 * h + 5 * m + 1 * f = 23.50 ∧ 5 * h + 9 * m + 1 * f = 39.50 → 2 * h + 2 * m + 2 * f = 15 := by
  (intros; linarith)
