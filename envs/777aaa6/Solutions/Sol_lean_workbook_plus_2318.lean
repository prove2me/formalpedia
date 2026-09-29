-- Prove2me | solution 1 for lean_workbook_plus_2318
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:39.622862+00:00
-- url     : https://prove2.me/submissions/2221e5aa-e7ed-4b45-8238-14fdb2a8e3c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 82 / 125) : x = 0.656 := by
  (intros; linarith)
