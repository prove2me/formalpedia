-- Prove2me | solution 1 for lean_workbook_plus_40204
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:45.871774+00:00
-- url     : https://prove2.me/submissions/1c54bdca-c2ec-4d02-9796-f00a4a8d276d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a b : ℝ) (hx : x = 1) (ha : a = 10) (hb : b = 4) : b > a/3 := by
  (intros; linarith)
