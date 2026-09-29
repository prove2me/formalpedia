-- Prove2me | solution 1 for lean_workbook_plus_19272
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:10.339831+00:00
-- url     : https://prove2.me/submissions/ee4af1fb-4431-4ce5-a7ae-a876da06794f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 6 * 3 * x = 4 * 9 * 3) :
  x = 6 := by
  (intros; linarith)
