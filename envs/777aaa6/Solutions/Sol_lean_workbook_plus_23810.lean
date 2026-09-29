-- Prove2me | solution 1 for lean_workbook_plus_23810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:33.378571+00:00
-- url     : https://prove2.me/submissions/7dfe7173-cfdc-476b-8a54-295da85a45fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a^3 - 3*a + 1 = 0) : (a^2 - 2)^3 - 3*(a^2 - 2) + 1 = 0 := by
  (intros; nlinarith [sq_nonneg (a)])
