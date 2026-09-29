-- Prove2me | solution 1 for lean_workbook_plus_19206
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:03.154955+00:00
-- url     : https://prove2.me/submissions/0f009ea7-fae8-484f-8d7f-786ef41da88e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 7 + Real.sqrt 50 + 7 - Real.sqrt 50 = 14 := by
  (intros; linarith)
