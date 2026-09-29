-- Prove2me | solution 1 for lean_workbook_plus_20207
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:19.100844+00:00
-- url     : https://prove2.me/submissions/f99d344f-344a-450b-87c3-420d75747b09

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^3 - 14 * x^2 + 48 * x + 192 = x * ((x - 7)^2 - 1) + 192 := by
  (intros; linarith)
