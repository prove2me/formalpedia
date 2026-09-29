-- Prove2me | solution 1 for lean_workbook_plus_1487
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:11.099175+00:00
-- url     : https://prove2.me/submissions/89350e85-8a7d-40b3-91d5-37a8d4cccec1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2 * b + a * b^2 - 2 * b^3)^2 + (a^3 - 2 * b^3 + a * b^2)^2 ≥ 0 := by
  (intros; positivity)
