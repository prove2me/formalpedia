-- Prove2me | solution 1 for lean_workbook_plus_26247
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:13.041277+00:00
-- url     : https://prove2.me/submissions/30737415-22e5-482e-a427-0222e7a3d22d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) :
  (a^2 + 3 * a) * (a^2 + 3 * a + 2) + 1 = (a^2 + 3 * a + 1)^2 := by
  (intros; linarith)
