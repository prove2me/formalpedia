-- Prove2me | solution 1 for lean_workbook_plus_67544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:53.703393+00:00
-- url     : https://prove2.me/submissions/5fd7e95e-0ab5-4642-9877-ce628294b17e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: 0 < x ∧ x < 10) : x^3 = x^3 := by
  norm_num
