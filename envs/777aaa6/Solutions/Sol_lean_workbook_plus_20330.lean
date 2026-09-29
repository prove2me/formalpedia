-- Prove2me | solution 1 for lean_workbook_plus_20330
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:29.279728+00:00
-- url     : https://prove2.me/submissions/a94d02fd-6d3b-44a9-8b16-d53cfaece69e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y:ℝ) (hy: y ≥ 0) : y^2 ≤ y + y^3 := by
  (intros; nlinarith [sq_nonneg (y)])
