-- Prove2me | solution 1 for lean_workbook_plus_22175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:54:45.153952+00:00
-- url     : https://prove2.me/submissions/3e34ed4d-f0d3-423e-bb54-1133f50d9ed0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≠ -Real.sqrt 2 / 2 ∧ x ≠ Real.sqrt 2 / 2) :
  x = x := by
  norm_num
