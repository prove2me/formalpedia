-- Prove2me | solution 1 for lean_workbook_plus_7915
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:56:53.18203+00:00
-- url     : https://prove2.me/submissions/a550d1f4-fca2-4147-bb23-0d30003c5a8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v : ℝ) : (u^3 - u^2 * v - 2 * u * v^2 + v^3)^2 ≥ 0 := by
  (intros; positivity)
