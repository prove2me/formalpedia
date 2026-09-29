-- Prove2me | solution 1 for lean_workbook_plus_15965
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:44.474789+00:00
-- url     : https://prove2.me/submissions/703f4e4d-4103-453d-9cce-671dc2b12f26

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : (a - b) ^ 2 ≥ 0) :
  a * b ≤ 1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 := by
  (intros; linarith)
