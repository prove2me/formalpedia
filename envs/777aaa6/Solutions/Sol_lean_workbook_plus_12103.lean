-- Prove2me | solution 1 for lean_workbook_plus_12103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:28.537257+00:00
-- url     : https://prove2.me/submissions/c7b0a8ec-e40c-4e2d-baf3-f519c23cb5b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w : ℝ)
  (h₀ : 6 = 1 / 3 * w) :
  w = 18 := by
  (intros; linarith)
