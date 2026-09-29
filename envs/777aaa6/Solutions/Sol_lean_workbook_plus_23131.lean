-- Prove2me | solution 1 for lean_workbook_plus_23131
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:47:17.4862+00:00
-- url     : https://prove2.me/submissions/1c326d17-68e5-4c8b-b9f5-b745ab93230f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^3 * y + x * y^3 ≤ x^4 + y^4 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
