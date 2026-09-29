-- Prove2me | solution 1 for lean_workbook_plus_65712
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:58.131522+00:00
-- url     : https://prove2.me/submissions/6ab66262-dfe3-42ec-b2d4-8ce3f71a19a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = 2) : 3 / (x^(1/9)) = 3 / (2^(1/9)) := by
  rfl
