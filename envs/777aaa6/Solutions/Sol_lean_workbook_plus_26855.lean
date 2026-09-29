-- Prove2me | solution 1 for lean_workbook_plus_26855
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:03:56.251861+00:00
-- url     : https://prove2.me/submissions/f4749dc4-f768-41c0-88cf-841e11d93c78

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  (3 * a^2 + b^2 + (2 * a^2 + 2 * b^2)) / 2 + (2 * b^2 + a^2 + b^2) / 2 = 3 * (a^2 + b^2) := by
  (intros; linarith)
