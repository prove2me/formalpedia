-- Prove2me | solution 1 for lean_workbook_plus_69906
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:12.219728+00:00
-- url     : https://prove2.me/submissions/253f6b9c-ba11-4ca7-b228-447fc9632bec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≥ 0) : x * (x - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
