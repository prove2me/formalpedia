-- Prove2me | solution 1 for lean_workbook_plus_34137
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:59.912858+00:00
-- url     : https://prove2.me/submissions/8855f0fd-540d-4596-a048-c6afadc86140

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 7 / 25) : x = 0.28 := by
  (intros; linarith)
