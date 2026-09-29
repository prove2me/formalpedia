-- Prove2me | solution 1 for lean_workbook_plus_64377
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:43.140187+00:00
-- url     : https://prove2.me/submissions/74a8191f-abc7-48f8-8b4c-457a4cb7c65a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a : ℝ) (hx: x ≥ 0) : (x + a)^2 = x^2 + 2 * a * x + a^2 := by
  (intros; linarith)
