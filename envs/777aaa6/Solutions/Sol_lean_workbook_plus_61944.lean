-- Prove2me | solution 1 for lean_workbook_plus_61944
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:08.453715+00:00
-- url     : https://prove2.me/submissions/4bb59d9a-fde2-4231-9ec1-c295a0dceb15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℚ) (hx : x = 3 / 4) : x = 0.75 := by
  (intros; linarith)
